#!/usr/bin/env python3
"""Item-level DAG library for FDRS spec items.

Builds a dependency graph from fdrs-index.yaml + item-deps.yaml +
item-deps-lean.yaml, computes the proof frontier, priority ordering,
and renders DOT/SVG visualizations.

Dependency sources (merged):
  - item-deps.yaml      — prose references from fdrs.md ("Definition 47")
  - item-deps-lean.yaml — Lean environment introspection (getUsedConstants)
"""

import subprocess
import sys
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path

try:
    import yaml
except ImportError:
    print("Error: PyYAML required. Install with: pip install pyyaml", file=sys.stderr)
    sys.exit(1)


@dataclass
class Node:
    id: str            # e.g. "theorem_42"
    type: str          # definition/theorem/proposition/lemma/corollary/gate/example
    global_num: int
    title: str
    phase: int
    fragment: str
    status: str        # proven/axiom/sorry/missing
    line: int          # fdrs.md line
    lean_files: list   # from index
    deps: list = field(default_factory=list)   # item IDs this depends on
    rdeps: list = field(default_factory=list)   # item IDs that depend on this


def build_dag(project_root: Path) -> dict[str, Node]:
    """Load index + deps and build the full item DAG.

    Returns dict keyed by item ID (e.g. "theorem_42").
    """
    index_path = project_root / "data" / "fdrs-index.yaml"
    deps_path = project_root / "data" / "item-deps.yaml"
    lean_deps_path = project_root / "data" / "item-deps-lean.yaml"

    with open(index_path) as f:
        index = yaml.safe_load(f)
    with open(deps_path) as f:
        deps_data = yaml.safe_load(f)

    # Build nodes from index
    dag: dict[str, Node] = {}
    for item in index["items"]:
        dag[item["id"]] = Node(
            id=item["id"],
            type=item["type"],
            global_num=item.get("global_num", 0),
            title=item.get("title", ""),
            phase=item["phase"],
            fragment=item.get("fragment", ""),
            status=item["status"],
            line=item["line"],
            lean_files=item.get("lean_files", []),
        )

    # Merge prose deps + lean deps (if available)
    all_edges = deps_data.get("dependencies", [])
    if lean_deps_path.exists():
        with open(lean_deps_path) as f:
            lean_deps = yaml.safe_load(f)
        all_edges.extend(lean_deps.get("dependencies", []))

    # Populate dep/rdep edges
    # "from" depends on "to"
    for edge in all_edges:
        src = edge["from"]  # the item that has the dependency
        tgt = edge["to"]    # the item being depended upon
        if src in dag and tgt in dag:
            if tgt not in dag[src].deps:
                dag[src].deps.append(tgt)
            if src not in dag[tgt].rdeps:
                dag[tgt].rdeps.append(src)

    return dag


def _transitive_rdep_count(dag: dict[str, Node], node_id: str) -> int:
    """Count the number of transitive reverse dependencies (downstream items)."""
    visited = set()
    queue = deque([node_id])
    while queue:
        nid = queue.popleft()
        for rdep in dag[nid].rdeps:
            if rdep not in visited:
                visited.add(rdep)
                queue.append(rdep)
    return len(visited)


def compute_frontier(dag: dict[str, Node]) -> list[Node]:
    """Items where status != 'proven' AND every dep has status == 'proven'.

    Sorted by downstream impact (most-unblocking first).
    """
    proven = {"proven"}
    frontier = []
    for node in dag.values():
        if node.status in proven:
            continue
        if all(dag[d].status in proven for d in node.deps):
            frontier.append(node)

    # Sort by transitive rdep count descending (most impact first)
    frontier.sort(key=lambda n: _transitive_rdep_count(dag, n.id), reverse=True)
    return frontier


def compute_blocked(dag: dict[str, Node]) -> list[tuple[Node, list[Node]]]:
    """Items where at least one dep is not proven.

    Returns each blocked item paired with its unproven deps.
    Sorted by fewest unproven deps first (closest to frontier).
    """
    proven = {"proven"}
    blocked = []
    for node in dag.values():
        if node.status in proven:
            continue
        unproven = [dag[d] for d in node.deps if dag[d].status not in proven]
        if unproven:
            blocked.append((node, unproven))

    blocked.sort(key=lambda pair: len(pair[1]))
    return blocked


def proof_priority(dag: dict[str, Node]) -> list[Node]:
    """Priority-ordered list of unproven items for proving work.

    Order: frontier items first (sorted by downstream impact), then
    near-frontier items (fewest unproven deps), then everything else.
    Only includes unproven items.
    """
    proven = {"proven"}
    frontier = []
    near = []
    deep = []

    for node in dag.values():
        if node.status in proven:
            continue
        unproven_deps = [d for d in node.deps if dag[d].status not in proven]
        if not unproven_deps:
            frontier.append(node)
        elif len(unproven_deps) <= 2:
            near.append((node, len(unproven_deps)))
        else:
            deep.append((node, len(unproven_deps)))

    frontier.sort(key=lambda n: _transitive_rdep_count(dag, n.id), reverse=True)
    near.sort(key=lambda pair: (pair[1], -_transitive_rdep_count(dag, pair[0].id)))
    deep.sort(key=lambda pair: (pair[1], -_transitive_rdep_count(dag, pair[0].id)))

    return frontier + [n for n, _ in near] + [n for n, _ in deep]


def render_item_dot(dag: dict[str, Node], output_path: Path, phase: int = None) -> None:
    """Generate DOT graph colored by proof status, optionally filtered by phase.

    Renders to SVG via graphviz if available.
    """
    status_colors = {
        "proven": "#c8e6c9",
        "axiom": "#bbdefb",
        "sorry": "#fff9c4",
        "missing": "#ef9a9a",
    }

    type_shapes = {
        "definition": "box",
        "gate": "diamond",
        "example": "box",
    }
    default_shape = "ellipse"  # theorems, propositions, lemmas, corollaries

    # Determine which nodes to include
    if phase is not None:
        phase_nodes = {nid for nid, n in dag.items() if n.phase == phase}
        # Also include cross-phase deps (dimmed)
        cross_deps = set()
        for nid in phase_nodes:
            for d in dag[nid].deps:
                if d not in phase_nodes:
                    cross_deps.add(d)
            for r in dag[nid].rdeps:
                if r not in phase_nodes:
                    cross_deps.add(r)
        visible = phase_nodes | cross_deps
    else:
        phase_nodes = set(dag.keys())
        cross_deps = set()
        visible = phase_nodes

    # Group nodes by phase for subgraph clusters
    phases: dict[int, list[str]] = {}
    for nid in visible:
        p = dag[nid].phase
        phases.setdefault(p, []).append(nid)

    lines = [
        "digraph fdrs_items {",
        '  rankdir=TB;',
        '  node [style=filled, fontsize=10];',
        '  edge [arrowsize=0.6, color="#888888"];',
        "",
    ]

    for p in sorted(phases):
        nids = sorted(phases[p], key=lambda nid: dag[nid].global_num)
        lines.append(f"  subgraph cluster_phase_{p} {{")
        lines.append(f'    label="Phase {p}";')
        lines.append('    style=dashed;')
        lines.append('    color="#999999";')
        lines.append("")

        for nid in nids:
            node = dag[nid]
            color = status_colors.get(node.status, "#e8e8e8")
            shape = type_shapes.get(node.type, default_shape)
            title = node.title[:30] + "..." if len(node.title) > 30 else node.title
            title = title.replace('\\', '\\\\').replace('"', '\\"')
            label = f"{node.type.capitalize()} {node.global_num}\\n{title}"

            # Dim cross-phase deps
            extra = ""
            if nid in cross_deps:
                extra = ', style="filled,dashed", fontcolor="#999999"'

            lines.append(f'    "{nid}" [label="{label}", fillcolor="{color}", shape={shape}{extra}];')

        lines.append("  }")
        lines.append("")

    # Edges (only between visible nodes)
    for nid in visible:
        for dep in dag[nid].deps:
            if dep in visible:
                style = ""
                if nid in cross_deps or dep in cross_deps:
                    style = ' [style=dashed, color="#cccccc"]'
                lines.append(f'  "{dep}" -> "{nid}"{style};')

    lines.append("}")

    dot_path = output_path.with_suffix(".dot")
    dot_path.write_text("\n".join(lines))

    try:
        subprocess.run(
            ["dot", "-Tsvg", str(dot_path), "-o", str(output_path)],
            check=True,
            capture_output=True,
        )
        print(f"Generated {output_path}")
    except FileNotFoundError:
        print(f"graphviz not found; DOT file saved to {dot_path}")
        print("Install graphviz and run: dot -Tsvg {dot_path} -o {output_path}")
    except subprocess.CalledProcessError as e:
        print(f"graphviz error: {e.stderr.decode()}")
        print(f"DOT file saved to {dot_path}")


def main():
    project_root = Path(__file__).resolve().parent.parent
    data_dir = project_root / "data"
    data_dir.mkdir(parents=True, exist_ok=True)

    dag = build_dag(project_root)

    # Per-phase graphs
    phases = sorted({n.phase for n in dag.values()})
    for p in phases:
        render_item_dot(dag, data_dir / f"item-graph-phase-{p}.svg", phase=p)

    # Full graph
    render_item_dot(dag, data_dir / "item-graph.svg")


if __name__ == "__main__":
    main()
