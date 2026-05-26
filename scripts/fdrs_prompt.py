#!/usr/bin/env python3
"""Specialist proof prompt generator for FDRS spec items.

Produces self-contained markdown prompts for proving agents, including
spec body text, dependency tables, Lean context, and notation references.
"""

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))


def extract_spec_text(fdrs_path: Path, start_line: int, next_item_line: int) -> str:
    """Extract the spec body text for an item from fdrs.md.

    Reads from start_line to next_item_line (or next heading of equal/higher level).
    Lines are 1-indexed (matching fdrs-index.yaml).
    """
    lines = fdrs_path.read_text().splitlines()
    # Convert to 0-indexed
    start = start_line - 1
    end = next_item_line - 1 if next_item_line else len(lines)

    # Trim trailing blank lines and horizontal rules
    body_lines = lines[start:end]
    while body_lines and body_lines[-1].strip() in ("", "---"):
        body_lines.pop()

    return "\n".join(body_lines)


def _find_next_item_line(dag: dict, current_id: str) -> int | None:
    """Find the fdrs.md line of the next spec item after current_id."""
    current = dag[current_id]
    # Collect all items sorted by line number
    by_line = sorted(dag.values(), key=lambda n: n.line)
    for i, node in enumerate(by_line):
        if node.id == current_id:
            if i + 1 < len(by_line):
                return by_line[i + 1].line
            return None
    return None


def get_lean_context(lean_file_path: str, project_root: Path) -> str:
    """Extract Lean declarations and imports for a given file.

    Uses lean_scan to find declarations in the file and its direct imports.
    """
    from lean_scan import scan_project

    scan = scan_project(project_root)

    lines = []

    # Imports for this file
    imports = [i for i in scan.imports if i.source_file == lean_file_path]
    if imports:
        lines.append("**Imports:**")
        for imp in imports:
            lines.append(f"- `import {imp.imported_module}`")
        lines.append("")

    # Declarations in this file
    decls = [d for d in scan.declarations if d.file == lean_file_path]
    if decls:
        lines.append("**Declarations in this file:**")
        for d in decls:
            lines.append(f"- `{d.kind} {d.name}` (line {d.line})")
        lines.append("")

    # Axioms in this file
    axioms = [a for a in scan.axioms if a.file == lean_file_path]
    if axioms:
        lines.append("**Axiom stubs in this file:**")
        for a in axioms:
            stub = " [TRUE STUB]" if a.is_true_stub else ""
            lines.append(f"- `axiom {a.name}` (line {a.line}){stub}")
            if a.type_sig:
                lines.append(f"  Type: `{a.type_sig[:120]}`")
        lines.append("")

    if not lines:
        lines.append("(no declarations found in this file)")

    return "\n".join(lines)


def _get_notation_subset(spec_body: str, project_root: Path) -> str:
    """Extract relevant notation entries based on symbols appearing in the spec body."""
    notation_path = project_root / "docs" / "notation.md"
    if not notation_path.exists():
        return "(notation.md not found — run `scripts/fdrs-summary --notation` to generate)"

    content = notation_path.read_text()

    # Collect matching data rows from all tables in notation.md
    matched_rows = []
    in_table = False
    for line in content.splitlines():
        if line.startswith("| Symbol") or line.startswith("| ----") or line.startswith("|---"):
            in_table = True
            continue
        if in_table and line.startswith("|"):
            # Check if any symbol in this row appears in the spec body
            m = re.search(r'`([^`]+)`', line)
            if m:
                symbol = m.group(1)
                if symbol in spec_body or symbol.replace("_", "") in spec_body:
                    matched_rows.append(line)
            else:
                # Key Symbols table rows don't use backticks — check raw cell
                cells = [c.strip() for c in line.split("|")[1:-1]]
                if cells and (cells[0] in spec_body or cells[0].replace("_", "") in spec_body):
                    matched_rows.append(line)
        elif in_table and not line.startswith("|"):
            in_table = False

    if not matched_rows:
        return "(no matching notations found for this item's spec text)"

    header = "| Symbol | Description | Source |\n|--------|-------------|--------|"
    return header + "\n" + "\n".join(matched_rows)


def generate_prompt(item_id: str, dag: dict, project_root: Path) -> str:
    """Generate a self-contained markdown prompt for proving a spec item."""
    node = dag[item_id]
    fdrs_path = project_root / "docs" / "fdrs.md"

    # Extract spec body text
    next_line = _find_next_item_line(dag, item_id)
    spec_body = extract_spec_text(fdrs_path, node.line, next_line)

    # Lean file info
    lean_file = node.lean_files[0]["path"] if node.lean_files else None
    lean_file_display = lean_file if lean_file else "not yet created"

    # Build dependency table
    dep_rows = []
    for dep_id in node.deps:
        dep = dag[dep_id]
        dep_lean = dep.lean_files[0]["path"] if dep.lean_files else "-"
        dep_rows.append(f"| {dep.id} | {dep.title[:40]} | {dep.status} | {dep_lean} |")

    dep_table = "| ID | Title | Status | Lean File |\n|---|---|---|---|\n"
    if dep_rows:
        dep_table += "\n".join(dep_rows)
    else:
        dep_table += "| (none) | — | — | — |"

    # Reverse deps (what this unblocks)
    rdep_lines = []
    for rdep_id in node.rdeps:
        rdep = dag[rdep_id]
        rdep_lines.append(f"- **{rdep.id}** — {rdep.title} ({rdep.status})")

    rdep_section = "\n".join(rdep_lines) if rdep_lines else "(nothing directly depends on this item)"

    # Lean context
    lean_context = ""
    if lean_file:
        lean_context = get_lean_context(lean_file, project_root)
    else:
        lean_context = "(no Lean file assigned yet)"

    # Notation subset
    notation = _get_notation_subset(spec_body, project_root)

    # Compute line range for doc comment
    end_line = (next_line - 1) if next_line else node.line + 20

    # Build the prompt
    sections = [
        f"# Task: Prove {node.type.capitalize()} {node.global_num} — {node.title}",
        "",
        "## Spec Reference",
        f"Phase {node.phase}, Fragment {node.fragment} | fdrs.md line {node.line}",
        "",
        spec_body,
        "",
        "## Status",
        f"Current: {node.status}",
        f"Lean file: {lean_file_display}",
        "",
        "## Dependencies",
        dep_table,
        "",
        "## What This Unblocks",
        rdep_section,
        "",
        "## Lean Context",
        f"File: {lean_file_display}",
        "",
        lean_context,
        "",
        "## Notation Reference",
        notation,
        "",
        "## Instructions",
        "1. The spec statement above is the ground truth.",
        f"2. Implement the proof in `{lean_file_display}`.",
        f"3. Include doc comment: `-- fdrs.md lines {node.line}-{end_line}, {node.type.capitalize()} {node.global_num}`",
        "4. After proving, run: `python3 scripts/fdrs-summary --rebuild && python3 scripts/fdrs-summary --check`",
    ]

    return "\n".join(sections)


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: fdrs_prompt.py ITEM_ID", file=sys.stderr)
        sys.exit(1)

    from fdrs_graph import build_dag

    project_root = Path(__file__).resolve().parent.parent
    dag = build_dag(project_root)

    item_id = sys.argv[1]
    if item_id not in dag:
        print(f"Error: '{item_id}' not found", file=sys.stderr)
        sys.exit(1)

    print(generate_prompt(item_id, dag, project_root))
