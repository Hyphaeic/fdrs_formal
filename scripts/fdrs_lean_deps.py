#!/usr/bin/env python3
"""Extract item-level dependencies from Lean's compiled environment.

Runs scripts/lean_deps.lean via `lake env lean` to get declaration-level
dependency edges from the Lean type checker, then maps them to
spec items via data/fdrs-index.yaml using per-item declaration lists.

Requires: `lake build` to have completed successfully.
Outputs:  data/item-deps-lean.yaml
"""

import subprocess
import sys
from collections import defaultdict
from pathlib import Path

try:
    import yaml
except ImportError:
    print("Error: PyYAML required. Install with: pip install pyyaml", file=sys.stderr)
    sys.exit(1)


def run_lean_deps(project_root: Path) -> list[tuple[str, str, str, str]]:
    """Run the Lean metaprogram and parse declaration-level edges from stdout.

    Returns list of (src_file, src_decl, tgt_file, tgt_decl) tuples.
    """
    script = project_root / "scripts" / "lean_deps.lean"

    result = subprocess.run(
        ["lake", "env", "lean", str(script)],
        cwd=project_root,
        capture_output=True,
        text=True,
        timeout=300,
    )

    if result.returncode != 0:
        stderr = result.stderr.strip()
        if "unknown module" in stderr or "file not found" in stderr.lower():
            print("  Error: project not built. Run `lake build` first.", file=sys.stderr)
        else:
            print(f"  Lean script failed (exit {result.returncode}):", file=sys.stderr)
            for line in stderr.split('\n')[-10:]:
                print(f"    {line}", file=sys.stderr)
        sys.exit(1)

    edges: list[tuple[str, str, str, str]] = []
    for line in result.stdout.strip().split("\n"):
        line = line.strip()
        if not line:
            continue
        parts = line.split("\t")
        if len(parts) == 4:
            edges.append((parts[0], parts[1], parts[2], parts[3]))
        elif len(parts) == 2:
            # Backwards compat: file-level only (old format)
            edges.append((parts[0], "", parts[1], ""))

    return edges


def build_decl_to_items(index_path: Path) -> tuple[dict[str, set[str]], dict[str, set[str]]]:
    """Build two mappings from the index:
    1. (file, decl_short_name) -> set of item IDs
    2. file -> set of item IDs (fallback for unmapped declarations)

    The index stores short declaration names (e.g. "inject") but Lean outputs
    fully-qualified names (e.g. "FdrsFormal.Composition.Injection.Definition.inject").
    We match by checking if the FQ name ends with the short name.
    """
    with open(index_path) as f:
        index = yaml.safe_load(f)

    # Map: (file_path, short_decl_name) -> set of item IDs
    decl_to_items: dict[tuple[str, str], set[str]] = defaultdict(set)
    # Map: file_path -> set of item IDs (fallback)
    file_to_items: dict[str, set[str]] = defaultdict(set)

    for item in index["items"]:
        item_id = item["id"]
        for lf in item.get("lean_files", []):
            path = lf["path"] if isinstance(lf, dict) else lf
            if not path:
                continue
            file_to_items[path].add(item_id)
            decls = lf.get("declarations", []) if isinstance(lf, dict) else []
            for d in decls:
                decl_to_items[(path, d)].add(item_id)

    return dict(decl_to_items), dict(file_to_items)


def resolve_decl_to_items(
    file_path: str,
    fq_decl: str,
    decl_to_items: dict[tuple[str, str], set[str]],
    file_to_items: dict[str, set[str]],
) -> set[str]:
    """Resolve a fully-qualified declaration name to its item IDs.

    Strategy:
    1. Try exact match with short name suffix against known declarations
    2. Fall back to file-level mapping (all items in that file)
    """
    # Extract short name variants to try
    # FQ: "FdrsFormal.Composition.Injection.Definition.inject"
    # Short names in index: "inject"
    # Try progressively shorter suffixes
    parts = fq_decl.split(".")
    for i in range(len(parts)):
        short = ".".join(parts[i:])
        key = (file_path, short)
        if key in decl_to_items:
            return decl_to_items[key]

    # Fallback: return all items in the file
    return file_to_items.get(file_path, set())


def build_item_signature(index_path: Path) -> dict[str, tuple]:
    """Build a signature for each item: sorted tuple of (file, sorted declarations).

    Items with identical signatures are indistinguishable to the dependency engine,
    so edges between them are spurious cross-product artifacts.
    """
    with open(index_path) as f:
        index = yaml.safe_load(f)

    sigs: dict[str, tuple] = {}
    for item in index["items"]:
        parts = []
        for lf in item.get("lean_files", []):
            path = lf["path"] if isinstance(lf, dict) else lf
            decls = tuple(sorted(lf.get("declarations", []))) if isinstance(lf, dict) else ()
            parts.append((path, decls))
        sigs[item["id"]] = tuple(sorted(parts))

    return sigs


def main():
    project_root = Path(__file__).resolve().parent.parent
    data_dir = project_root / "data"

    print("Building Lean-derived dependency graph...")
    raw_edges = run_lean_deps(project_root)
    print(f"  {len(raw_edges)} raw declaration-level edges from Lean environment")

    # Deduplicate file-level edges for stats
    file_edges = set((e[0], e[2]) for e in raw_edges)
    print(f"  {len(file_edges)} unique file-level edges")

    # Map to spec items using declaration-level precision
    decl_to_items, file_to_items = build_decl_to_items(data_dir / "fdrs-index.yaml")

    # Build item signatures to detect co-mapped items
    item_sigs = build_item_signature(data_dir / "fdrs-index.yaml")

    item_edges: set[tuple[str, str]] = set()
    unmapped_files: set[str] = set()
    decl_resolved = 0
    file_fallback = 0

    for src_file, src_decl, tgt_file, tgt_decl in raw_edges:
        # Resolve source declaration to items
        if src_decl:
            src_items = resolve_decl_to_items(src_file, src_decl, decl_to_items, file_to_items)
            if src_items != file_to_items.get(src_file, set()):
                decl_resolved += 1
            else:
                file_fallback += 1
        else:
            src_items = file_to_items.get(src_file, set())
            file_fallback += 1

        # Resolve target declaration to items
        if tgt_decl:
            tgt_items = resolve_decl_to_items(tgt_file, tgt_decl, decl_to_items, file_to_items)
        else:
            tgt_items = file_to_items.get(tgt_file, set())

        if not src_items:
            unmapped_files.add(src_file)
        if not tgt_items:
            unmapped_files.add(tgt_file)

        for si in src_items:
            for ti in tgt_items:
                if si != ti:
                    item_edges.add((si, ti))

    # Filter spurious edges: remove edges between items with identical signatures.
    # These are co-mapped items that share the exact same (files, declarations)
    # and are indistinguishable to the dependency engine.
    pre_filter = len(item_edges)
    item_edges = {
        (si, ti) for si, ti in item_edges
        if item_sigs.get(si) != item_sigs.get(ti)
    }
    spurious = pre_filter - len(item_edges)

    deps = [
        {"from": src, "to": tgt, "source": "lean"}
        for src, tgt in sorted(item_edges)
    ]

    output = {
        "metadata": {
            "total_file_edges": len(file_edges),
            "total_raw_edges": len(raw_edges),
            "total_item_edges": len(deps),
            "spurious_filtered": spurious,
            "unmapped_files": len(unmapped_files),
            "decl_resolved": decl_resolved,
            "file_fallback": file_fallback,
            "source": "lean_environment_decl_level",
        },
        "dependencies": deps,
    }

    output_path = data_dir / "item-deps-lean.yaml"
    with open(output_path, "w") as f:
        yaml.dump(output, f, default_flow_style=False, sort_keys=False, allow_unicode=True, width=120)

    print(f"  {output_path}: {len(deps)} item-level edges ({spurious} spurious filtered, {len(unmapped_files)} unmapped files)")
    print(f"  Resolution: {decl_resolved} decl-level, {file_fallback} file-level fallback")


if __name__ == "__main__":
    main()
