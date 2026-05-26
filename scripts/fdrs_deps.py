#!/usr/bin/env python3
"""Extract dependency graphs: file-level (from imports) and item-level (from fdrs.md references).

Outputs:
  data/file-deps.yaml   - Lean file import graph
  data/item-deps.yaml   - Mathematical item dependency graph
  docs/dependency-graph.svg - Rendered file dependency graph (requires graphviz)
"""

import re
import sys
import json
from pathlib import Path

try:
    import yaml
except ImportError:
    print("Error: PyYAML required. Install with: pip install pyyaml", file=sys.stderr)
    sys.exit(1)

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_scan import scan_project
from fdrs_parse import parse_fdrs


def build_file_deps(project_root: Path) -> dict:
    """Build file-level dependency graph from import statements."""
    scan = scan_project(project_root)

    # Convert module names to file paths
    edges: list[dict] = []
    nodes: set[str] = set()

    for imp in scan.imports:
        source = imp.source_file
        # Convert module path to file path guess
        target_path = imp.imported_module.replace('.', '/') + '.lean'
        target_dir = imp.imported_module.replace('.', '/')

        # Check if it's a file or directory import
        if (project_root / target_path).exists():
            target = target_path
        elif (project_root / target_dir).is_dir():
            # Directory import - find the root .lean file
            root_lean = target_dir + '.lean'
            if (project_root / root_lean).exists():
                target = root_lean
            else:
                target = target_dir + '/'
        else:
            target = target_path  # Best guess

        nodes.add(source)
        nodes.add(target)
        edges.append({'from': source, 'to': target})

    # Compute module-level summary
    modules: dict[str, set[str]] = {}
    for node in nodes:
        parts = node.split('/')
        if len(parts) >= 2 and parts[0] == 'FdrsFormal':
            module = parts[1]
            modules.setdefault(module, set()).add(node)

    module_edges: list[dict] = []
    seen_module_edges = set()
    for edge in edges:
        src_parts = edge['from'].split('/')
        tgt_parts = edge['to'].split('/')
        if len(src_parts) >= 2 and len(tgt_parts) >= 2:
            src_mod = src_parts[1]
            tgt_mod = tgt_parts[1]
            if src_mod != tgt_mod:
                key = (src_mod, tgt_mod)
                if key not in seen_module_edges:
                    seen_module_edges.add(key)
                    module_edges.append({'from': src_mod, 'to': tgt_mod})

    return {
        'metadata': {
            'total_files': len(nodes),
            'total_edges': len(edges),
            'total_modules': len(modules),
        },
        'modules': {name: sorted(files) for name, files in sorted(modules.items())},
        'module_edges': module_edges,
        'file_edges': edges,
    }


def build_item_deps(project_root: Path) -> dict:
    """Build item-level dependency graph from fdrs.md textual references."""
    items = parse_fdrs(project_root / "docs" / "fdrs.md")
    fdrs_text = (project_root / "docs" / "fdrs.md").read_text().splitlines()

    # Build item lookup by (type, number)
    item_by_type_num: dict[tuple[str, str], list] = {}
    for item in items:
        item_by_type_num.setdefault((item.type, str(item.global_num)), []).append(item)

    # Reference patterns
    RE_REF = re.compile(
        r'(?:by\s+|from\s+|see\s+|via\s+|using\s+)?'
        r'(Definition|Theorem|Proposition|Lemma|Corollary|Gate|Example)\s+'
        r'(\d+(?:\.\d+)*)',
        re.IGNORECASE
    )

    # For each item, scan its body (from item.line to next item's line) for references
    item_lines = sorted([(item.line, item) for item in items])

    deps: list[dict] = []
    for idx, (line, item) in enumerate(item_lines):
        # Body extends to next item or +50 lines
        end_line = item_lines[idx + 1][0] if idx + 1 < len(item_lines) else line + 50
        end_line = min(end_line, len(fdrs_text))

        body = '\n'.join(fdrs_text[line:end_line])

        for m in RE_REF.finditer(body):
            ref_type = m.group(1).lower()
            ref_num = m.group(2)
            if ref_type == item.type and ref_num == str(item.global_num):
                continue  # skip self-reference
            targets = item_by_type_num.get((ref_type, ref_num), [])
            for target in targets:
                # Only keep backward references (to earlier items).
                # Forward references (item mentions a later item) are
                # motivational, not mathematical dependencies.
                if target.global_num >= item.global_num:
                    continue
                deps.append({
                    'from': item.id,
                    'to': target.id,
                    'ref_number': ref_num,
                })

    return {
        'metadata': {
            'total_items': len(items),
            'total_deps': len(deps),
        },
        'dependencies': deps,
    }


def render_dot(file_deps: dict, output_path: Path):
    """Render module-level dependency graph to DOT format and SVG."""
    dot_lines = [
        'digraph fdrs_modules {',
        '  rankdir=TB;',
        '  node [shape=box, style=filled, fillcolor="#e8e8e8"];',
        '',
    ]

    # Module colors
    colors = {
        'Core': '#c8e6c9',
        'Operations': '#bbdefb',
        'Topology': '#d1c4e9',
        'FunctionSpaces': '#ffe0b2',
        'NumberTheory': '#f8bbd0',
        'Integration': '#b2dfdb',
        'Modes': '#fff9c4',
        'Composition': '#ffccbc',
    }

    modules = set()
    for edge in file_deps.get('module_edges', []):
        modules.add(edge['from'])
        modules.add(edge['to'])

    for mod in sorted(modules):
        color = colors.get(mod, '#e8e8e8')
        dot_lines.append(f'  "{mod}" [fillcolor="{color}"];')

    dot_lines.append('')

    for edge in file_deps.get('module_edges', []):
        dot_lines.append(f'  "{edge["from"]}" -> "{edge["to"]}";')

    dot_lines.append('}')

    dot_path = output_path.with_suffix('.dot')
    dot_path.write_text('\n'.join(dot_lines))

    # Try to render SVG
    import subprocess
    try:
        subprocess.run(
            ['dot', '-Tsvg', str(dot_path), '-o', str(output_path)],
            check=True, capture_output=True
        )
        print(f"Generated {output_path}")
    except FileNotFoundError:
        print(f"graphviz not found; DOT file saved to {dot_path}")
        print("Install graphviz and run: dot -Tsvg docs/dependency-graph.dot -o docs/dependency-graph.svg")
    except subprocess.CalledProcessError as e:
        print(f"graphviz error: {e.stderr.decode()}")
        print(f"DOT file saved to {dot_path}")


def main():
    project_root = Path(__file__).resolve().parent.parent
    data_dir = project_root / "data"
    data_dir.mkdir(parents=True, exist_ok=True)

    # File-level deps
    print("Building file dependency graph...")
    file_deps = build_file_deps(project_root)
    file_deps_path = data_dir / "file-deps.yaml"
    with open(file_deps_path, 'w') as f:
        yaml.dump(file_deps, f, default_flow_style=False, sort_keys=False, allow_unicode=True, width=120)
    print(f"  {file_deps_path}: {file_deps['metadata']['total_files']} files, {file_deps['metadata']['total_edges']} edges")

    # Item-level deps
    print("Building item dependency graph...")
    item_deps = build_item_deps(project_root)
    item_deps_path = data_dir / "item-deps.yaml"
    with open(item_deps_path, 'w') as f:
        yaml.dump(item_deps, f, default_flow_style=False, sort_keys=False, allow_unicode=True, width=120)
    print(f"  {item_deps_path}: {item_deps['metadata']['total_items']} items, {item_deps['metadata']['total_deps']} deps")

    # Render graph
    print("Rendering dependency graph...")
    svg_path = project_root / "docs" / "dependency-graph.svg"
    render_dot(file_deps, svg_path)


if __name__ == "__main__":
    main()
