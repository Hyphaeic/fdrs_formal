#!/usr/bin/env python3
"""Cross-reference fdrs.md items with Lean declarations and output data/fdrs-index.yaml.

Joining strategies (in priority order):
1. fdrs.md line-range annotations in Lean doc comments
2. Phase/fragment matching from Lean module-level doc comments
3. Fuzzy title/name matching as fallback
"""

import re
import sys
import datetime
from pathlib import Path
from typing import Optional

try:
    import yaml
except ImportError:
    print("Error: PyYAML required. Install with: pip install pyyaml", file=sys.stderr)
    sys.exit(1)

# Import sibling modules
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fdrs_parse import parse_fdrs, SpecItem
from lean_scan import scan_project, LeanScanResult, Declaration, AxiomDecl


def extract_line_ranges(fdrs_refs):
    """Extract (file, start_line, end_line) from fdrs.md references."""
    RE_LINES = re.compile(r'lines?\s+(\d+)\s*[-–to]+\s*(\d+)', re.IGNORECASE)
    RE_LINE_SINGLE = re.compile(r'line\s+(\d+)', re.IGNORECASE)
    ranges = []
    for ref in fdrs_refs:
        m = RE_LINES.search(ref.text)
        if m:
            ranges.append((ref.file, int(m.group(1)), int(m.group(2))))
        else:
            m = RE_LINE_SINGLE.search(ref.text)
            if m:
                ln = int(m.group(1))
                ranges.append((ref.file, ln, ln + 50))
    return ranges


def extract_phase_fragment_refs(fdrs_refs):
    """Extract (file, phase, fragment) from fdrs.md references like 'Phase 1 Fragment 2'."""
    RE_PF = re.compile(r'Phase\s+(\d+)(?:\s*,?\s*Fragment\s+(\S+))?', re.IGNORECASE)
    results = []
    for ref in fdrs_refs:
        m = RE_PF.search(ref.text)
        if m:
            phase = int(m.group(1))
            frag = m.group(2)
            results.append((ref.file, phase, frag))
    return results


def _name_words(name: str) -> set[str]:
    """Split a camelCase/snake_case identifier into lowercase words."""
    parts = re.findall(r'[A-Z]?[a-z]+|[A-Z]+(?=[A-Z][a-z]|\d|\b)', name)
    return {w.lower() for w in parts}


def _title_words(title: str) -> set[str]:
    """Extract lowercase words (3+ chars) from a spec item title."""
    return {w.lower() for w in re.findall(r'[a-zA-Z]{3,}', title)}


def _find_item_decls(item: 'SpecItem', decls: list[Declaration]) -> list[Declaration]:
    """Find declarations in a file that likely correspond to a specific spec item.

    Uses the item's title words to score each declaration name. Returns only
    declarations that score >= 2 word matches. If none score high enough,
    returns empty list (caller should fall back to file-level check).
    """
    if not item.title:
        return []
    twords = _title_words(item.title)
    if not twords:
        return []

    scored: list[tuple[Declaration, int]] = []
    for d in decls:
        dwords = _name_words(d.name)
        overlap = len(twords & dwords)
        if overlap >= 2:
            scored.append((d, overlap))

    scored.sort(key=lambda x: -x[1])
    return [d for d, _ in scored[:5]]


def _decl_scaffold(d: Declaration) -> bool:
    return getattr(d, 'scaffold_kind', None) is not None or d.stub_kind is not None


def _decl_genuine(d: Declaration) -> bool:
    return d.stub_kind is None and getattr(d, 'scaffold_kind', None) is None


def _classify_decls(decls: list[Declaration]) -> tuple[bool, bool]:
    """Return (has_genuine, has_scaffold) for a list of declarations."""
    return any(_decl_genuine(d) for d in decls), any(_decl_scaffold(d) for d in decls)


def _item_status(has_lean: bool, has_genuine: bool, has_scaffold: bool,
                 has_sorry: bool, has_axiom: bool, in_root: bool) -> str:
    """Compute item status under the publication-readiness category model.

    Precedence is conservative — a scaffold or sorry anywhere associated with the
    item prevents a `proven` label, and genuine content that lives only outside the
    root build is reported as `excluded` rather than `proven`.
    """
    if not has_lean:
        return 'missing'
    if has_sorry:
        return 'wip'
    if has_scaffold:
        return 'scaffold'
    if has_genuine:
        return 'proven' if in_root else 'excluded'
    if has_axiom:
        return 'axiom'
    return 'missing'


def _file_to_module(f: str) -> str:
    return f[:-5].replace('/', '.') if f.endswith('.lean') else f


def _module_to_file(m: str) -> str:
    return m.replace('.', '/') + '.lean'


def _root_reachable_files(scan: LeanScanResult, project_root: Path) -> set[str]:
    """Files reachable by import from the root module `FdrsFormal` (the default build).

    Modules present in the tree but not in this set compile only when named
    explicitly; items living solely in them are reported as `excluded`.
    """
    adj: dict[str, set[str]] = {}
    for imp in scan.imports:
        adj.setdefault(_file_to_module(imp.source_file), set()).add(imp.imported_module)

    roots = ['FdrsFormal']
    root_file = project_root / 'FdrsFormal.lean'
    if root_file.exists():
        for line in root_file.read_text().splitlines():
            m = re.match(r'^\s*import\s+(FdrsFormal\S*)', line)
            if m:
                roots.append(m.group(1))

    seen: set[str] = set()
    stack = list(roots)
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        stack.extend(d for d in adj.get(mod, ()) if d not in seen)
    return {_module_to_file(m) for m in seen}


_STALE_CLAIM_RE = re.compile(
    r'[1-9]\d*\s+axioms?\b|axioms?\s+created|pure axioms|axiom\s+stub|🔵',
    re.IGNORECASE,
)


def _detect_stale_docs(scan: LeanScanResult, project_root: Path) -> list[dict]:
    """Flag files whose comments claim axioms/stubs that no longer exist in live code.

    Conservative: only fires while the repo has zero live axioms, so any comment
    asserting N>0 axioms / 'axiomatized' / 'STUB' is provably stale.
    """
    if len(scan.axioms) != 0:
        return []
    risks: list[dict] = []
    lean_dir = project_root / 'FdrsFormal'
    files = sorted(lean_dir.rglob('*.lean'))
    extra = project_root / 'FdrsFormal.lean'
    if extra.exists():
        files.append(extra)
    for fp in files:
        try:
            text = fp.read_text()
        except Exception:
            continue
        hits = [(i + 1, ln.strip()) for i, ln in enumerate(text.splitlines())
                if _STALE_CLAIM_RE.search(ln)]
        if hits:
            risks.append({
                'file': str(fp.relative_to(project_root)),
                'lines': [h[0] for h in hits[:6]],
                'claims': [h[1][:90] for h in hits[:6]],
            })
    return risks


def _link_scaffold_items(index_items: list[dict], scaffold_decls: list[Declaration]) -> int:
    """Reverse pass: map each scaffold *declaration* to the spec item it most likely
    names (by declaration-name ↔ item-title word overlap) and ensure that item is not
    labelled `proven`.

    The forward matcher links items to files coarsely (often the aggregator), so a
    scaffold declaration's item can slip through as `proven`. This corrects that using
    the *exact* scaffold set. Only downgrades proven→scaffold (never the reverse), and
    records the linking declaration for traceability.
    """
    title_index = [(it, _title_words(it['title'])) for it in index_items if it.get('title')]
    downgraded = 0
    for d in scaffold_decls:
        dwords = _name_words(d.name)
        if not dwords:
            continue
        best, best_ov = None, 1  # require ≥ 2 overlapping words
        for it, tw in title_index:
            ov = len(dwords & tw)
            if ov > best_ov:
                best, best_ov = it, ov
        if best is not None:
            best.setdefault('scaffold_decls', []).append(f"{d.file}:{d.line} {d.name}")
            if best['status'] == 'proven':
                best['status'] = 'scaffold'
                downgraded += 1
    return downgraded


def match_items_to_lean(
    items: list[SpecItem],
    scan: LeanScanResult,
    root_files: set[str],
) -> dict[str, dict]:
    """Match spec items to Lean declarations. Returns item_id -> match_info."""
    matches: dict[str, dict] = {}

    # Build lookup structures
    line_ranges = extract_line_ranges(scan.fdrs_refs)
    pf_refs = extract_phase_fragment_refs(scan.fdrs_refs)

    # Build file -> declarations map
    file_decls: dict[str, list[Declaration]] = {}
    for d in scan.declarations:
        file_decls.setdefault(d.file, []).append(d)

    # Build file -> axioms map
    file_axioms: dict[str, list[AxiomDecl]] = {}
    for a in scan.axioms:
        file_axioms.setdefault(a.file, []).append(a)

    # Build sorry files set
    sorry_files: dict[str, list[int]] = {}
    for s in scan.sorries:
        sorry_files.setdefault(s.file, []).append(s.line)

    # Strategy 1: line-range matching
    for item in items:
        item_line = item.line
        matched_files = set()
        for file_path, start, end in line_ranges:
            if start <= item_line <= end:
                matched_files.add(file_path)

        if matched_files:
            lean_files = []
            has_axiom = False
            has_sorry = False
            has_genuine_proof = False
            has_stub = False
            for fp in sorted(matched_files):
                fp_decls = file_decls.get(fp, [])
                axiom_names = [a.name for a in file_axioms.get(fp, [])]
                lean_files.append({
                    'path': fp,
                    'declarations': [d.name for d in fp_decls][:10],
                })
                if axiom_names:
                    has_axiom = True
                if fp in sorry_files:
                    has_sorry = True

                # Try to narrow to item-specific declarations
                item_decls = _find_item_decls(item, fp_decls)
                if item_decls:
                    g, s = _classify_decls(item_decls)
                    if g: has_genuine_proof = True
                    if s: has_stub = True
                else:
                    # No item-specific name match: the file-level fallback provides
                    # proof evidence only. Scaffold/wip is attributed solely via the
                    # specific declaration matches above, so a genuine item is never
                    # mislabelled just for sharing a file/phase with a scaffold; the
                    # exact scaffold set is reported separately at declaration level.
                    if any(_decl_genuine(d) for d in fp_decls):
                        has_genuine_proof = True

            in_root = any(lf['path'] in root_files for lf in lean_files)
            status = _item_status(
                has_lean=bool(lean_files),
                has_genuine=has_genuine_proof, has_scaffold=has_stub,
                has_sorry=has_sorry, has_axiom=has_axiom, in_root=in_root,
            )
            matches[item.id] = {
                'lean_files': lean_files,
                'status': status,
                'match_method': 'line_range',
                'in_root_build': in_root,
            }

    # Strategy 2: phase/fragment matching for unmatched items
    # Build phase_frag -> files map
    pf_to_files: dict[tuple, set[str]] = {}
    for file_path, phase, frag in pf_refs:
        key = (phase, frag)
        pf_to_files.setdefault(key, set()).add(file_path)
        # Also add (phase, None) as a fallback
        pf_to_files.setdefault((phase, None), set()).add(file_path)

    for item in items:
        if item.id in matches:
            continue

        # Try exact phase+fragment match
        key = (item.phase, item.fragment)
        candidate_files = pf_to_files.get(key, set())

        # Also try phase-only match
        if not candidate_files:
            key = (item.phase, None)
            candidate_files = pf_to_files.get(key, set())

        if candidate_files:
            lean_files = []
            has_axiom = False
            has_sorry = False
            has_genuine_proof = False
            has_stub = False

            for fp in sorted(candidate_files):
                fp_decls = file_decls.get(fp, [])
                axiom_names = [a.name for a in file_axioms.get(fp, [])]
                decl_names = [d.name for d in fp_decls]
                if axiom_names or decl_names:
                    lean_files.append({
                        'path': fp,
                        'declarations': (decl_names + axiom_names)[:5],
                    })
                if axiom_names:
                    has_axiom = True
                if fp in sorry_files:
                    has_sorry = True

                # Try to narrow to item-specific declarations
                item_decls = _find_item_decls(item, fp_decls)
                if item_decls:
                    g, s = _classify_decls(item_decls)
                    if g: has_genuine_proof = True
                    if s: has_stub = True
                else:
                    # No item-specific name match: fallback provides proof evidence only
                    # (scaffold/wip is attributed via specific declaration matches).
                    if any(_decl_genuine(d) for d in fp_decls):
                        has_genuine_proof = True

            if lean_files:
                in_root = any(lf['path'] in root_files for lf in lean_files)
                status = _item_status(
                    has_lean=True,
                    has_genuine=has_genuine_proof, has_scaffold=has_stub,
                    has_sorry=has_sorry, has_axiom=has_axiom, in_root=in_root,
                )
                matches[item.id] = {
                    'lean_files': lean_files[:5],  # Cap at 5 files
                    'status': status,
                    'match_method': 'phase_fragment',
                    'in_root_build': in_root,
                }

    # Strategy 3: fuzzy name matching for remaining unmatched
    # Build a name index for declarations
    name_index: dict[str, list[Declaration]] = {}
    for d in scan.declarations:
        # Normalize: split camelCase, lowercase
        words = re.findall(r'[A-Z]?[a-z]+|[A-Z]+(?=[A-Z][a-z]|\d|\b)', d.name)
        for w in words:
            name_index.setdefault(w.lower(), []).append(d)

    for item in items:
        if item.id in matches:
            continue

        if not item.title:
            matches[item.id] = {'lean_files': [], 'status': 'missing', 'match_method': 'none'}
            continue

        # Extract key words from title
        title_words = re.findall(r'[a-zA-Z]{3,}', item.title.lower())
        candidate_decls: dict[str, int] = {}  # decl name -> score

        for word in title_words:
            for d in name_index.get(word, []):
                candidate_decls[d.name] = candidate_decls.get(d.name, 0) + 1

        if candidate_decls:
            best = sorted(candidate_decls.items(), key=lambda x: -x[1])[:3]
            if best[0][1] >= 2:  # At least 2 matching words
                matched_decl_names = [name for name, _ in best]
                lean_files = []
                has_genuine = False
                has_scaffold = False
                has_sorry = False
                for d in scan.declarations:
                    if d.name in matched_decl_names:
                        lean_files.append({
                            'path': d.file,
                            'declarations': [d.name],
                        })
                        if _decl_genuine(d):
                            has_genuine = True
                        if _decl_scaffold(d):
                            has_scaffold = True
                        if d.file in sorry_files:
                            has_sorry = True

                in_root = any(lf['path'] in root_files for lf in lean_files)
                status = _item_status(
                    has_lean=bool(lean_files),
                    has_genuine=has_genuine, has_scaffold=has_scaffold,
                    has_sorry=has_sorry, has_axiom=False, in_root=in_root,
                )
                matches[item.id] = {
                    'lean_files': lean_files[:3],
                    'status': status,
                    'match_method': 'fuzzy_name',
                    'in_root_build': in_root,
                }
            else:
                matches[item.id] = {'lean_files': [], 'status': 'missing', 'match_method': 'none'}
        else:
            matches[item.id] = {'lean_files': [], 'status': 'missing', 'match_method': 'none'}

    return matches


def build_index(project_root: Path) -> dict:
    """Build the complete index."""
    fdrs_path = project_root / "docs" / "fdrs.md"
    spec_lines = len(fdrs_path.read_text().splitlines())

    items = parse_fdrs(fdrs_path)
    scan = scan_project(project_root)
    root_files = _root_reachable_files(scan, project_root)
    matches = match_items_to_lean(items, scan, root_files)
    stale_docs = _detect_stale_docs(scan, project_root)

    # Build items list
    index_items = []
    for item in items:
        match_info = matches.get(item.id, {'lean_files': [], 'status': 'missing', 'match_method': 'none'})
        entry = {
            'id': item.id,
            'type': item.type,
            'phase': item.phase,
            'global_num': item.global_num,
            'title': item.title,
            'line': item.line,
            'status': match_info['status'],
            'in_root_build': match_info.get('in_root_build', True),
            'lean_files': match_info['lean_files'],
        }
        if item.fragment:
            entry['fragment'] = item.fragment
        if item.section:
            entry['section'] = item.section
        index_items.append(entry)

    scaffold_decls = [d for d in scan.declarations if getattr(d, 'scaffold_kind', None) is not None]
    # Reverse pass: a scaffold declaration's owning spec item must not read 'proven'.
    _link_scaffold_items(index_items, scaffold_decls)

    # Status counts (after the reverse pass)
    status_counts = {}
    for item in index_items:
        s = item['status']
        status_counts[s] = status_counts.get(s, 0) + 1

    all_files = {d.file for d in scan.declarations} | {imp.source_file for imp in scan.imports}
    excluded_modules = sorted(f for f in all_files if f not in root_files)

    index = {
        'metadata': {
            'spec_file': 'docs/fdrs.md',
            'spec_lines': spec_lines,
            'generated_at': datetime.datetime.now().isoformat(),
            'total_items': len(index_items),
            'status_summary': status_counts,
            'status_legend': {
                'proven': 'meaningful statement, no sorry/axiom/scaffold, in the default build',
                'scaffold': 'compiles but vacuous/placeholder/constantized/weakened',
                'wip': 'contains a sorry',
                'excluded': 'genuine, but only in modules outside the default root build',
                'axiom': 'backed by an axiom',
                'missing': 'no matched Lean declaration',
            },
        },
        'items': index_items,
        'lean_summary': {
            'total_files': scan.total_files,
            'total_axioms': len(scan.axioms),
            'axioms_true': sum(1 for a in scan.axioms if a.is_true_stub),
            'total_sorries': len(scan.sorries),
            'sorry_files': [
                {'file': s.file, 'line': s.line, 'context': s.context[:200]}
                for s in scan.sorries
            ],
            'total_theorems': sum(1 for d in scan.declarations if d.kind == 'theorem'),
            'total_defs': sum(1 for d in scan.declarations if d.kind == 'def'),
            'total_lemmas': sum(1 for d in scan.declarations if d.kind == 'lemma'),
            'total_stubs': sum(1 for d in scan.declarations if d.stub_kind is not None),
            'stubs_by_kind': {
                'true_trivial': sum(1 for d in scan.declarations if d.stub_kind == 'true_trivial'),
                'prop_true': sum(1 for d in scan.declarations if d.stub_kind == 'prop_true'),
                'zero_impl': sum(1 for d in scan.declarations if d.stub_kind == 'zero_impl'),
            },
            'total_scaffold': len(scaffold_decls),
            'scaffold_by_severity': {
                'high': sum(1 for d in scaffold_decls if d.scaffold_severity == 'high'),
                'low': sum(1 for d in scaffold_decls if d.scaffold_severity == 'low'),
            },
            'scaffold_declarations': [
                {'file': d.file, 'line': d.line, 'kind': d.kind, 'name': d.name,
                 'scaffold_kind': d.scaffold_kind, 'severity': d.scaffold_severity}
                for d in scaffold_decls
            ],
            'excluded_modules': excluded_modules,
            'stale_doc_risks': stale_docs,
        },
    }

    return index


def main():
    project_root = Path(__file__).resolve().parent.parent
    index = build_index(project_root)

    output_path = project_root / "data" / "fdrs-index.yaml"
    output_path.parent.mkdir(parents=True, exist_ok=True)

    with open(output_path, 'w') as f:
        yaml.dump(index, f, default_flow_style=False, sort_keys=False, allow_unicode=True, width=120)

    print(f"Generated {output_path}")
    meta = index['metadata']
    print(f"  Total items: {meta['total_items']}")
    print(f"  Status: {meta['status_summary']}")
    ls = index['lean_summary']
    print(f"  Lean files: {ls['total_files']}")
    print(f"  Axioms: {ls['total_axioms']} ({ls['axioms_true']} True stubs)")
    print(f"  Sorries: {ls['total_sorries']}")
    print(f"  Declaration stubs: {ls['total_stubs']} ({ls['stubs_by_kind']})")
    sv = ls['scaffold_by_severity']
    print(f"  Scaffold declarations: {ls['total_scaffold']} ({sv['high']} high / {sv['low']} low)")
    print(f"  Excluded (non-root) modules: {len(ls['excluded_modules'])}")
    print(f"  Stale-doc-risk files: {len(ls['stale_doc_risks'])}")


if __name__ == "__main__":
    main()
