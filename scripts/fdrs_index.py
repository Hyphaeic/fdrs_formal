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


def _classify_decls(decls: list[Declaration]) -> tuple[bool, bool]:
    """Return (has_genuine, has_stub) for a list of declarations."""
    has_genuine = any(d.stub_kind is None for d in decls)
    has_stub = any(d.stub_kind is not None for d in decls)
    return has_genuine, has_stub


def match_items_to_lean(
    items: list[SpecItem],
    scan: LeanScanResult,
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
                    # No item-specific match; assume proven if file has any
                    # genuine declarations (don't blame this item for stubs
                    # that might belong to other items in the same file)
                    if any(d.stub_kind is None for d in fp_decls) and fp not in sorry_files:
                        has_genuine_proof = True

            status = "missing"
            if has_genuine_proof and has_stub:
                status = "partial"
            elif has_genuine_proof:
                status = "proven"
            elif has_stub:
                status = "stub"
            elif has_sorry:
                status = "sorry"
            elif has_axiom:
                status = "axiom"

            matches[item.id] = {
                'lean_files': lean_files,
                'status': status,
                'match_method': 'line_range',
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
                    # No item-specific match; assume proven if file has any
                    # genuine declarations (don't blame this item for stubs
                    # that might belong to other items in the same file)
                    if any(d.stub_kind is None for d in fp_decls):
                        has_genuine_proof = True

            if lean_files:
                status = "missing"
                if has_genuine_proof and has_stub:
                    status = "partial"
                elif has_genuine_proof:
                    status = "proven"
                elif has_stub:
                    status = "stub"
                elif has_sorry:
                    status = "sorry"
                elif has_axiom:
                    status = "axiom"

                matches[item.id] = {
                    'lean_files': lean_files[:5],  # Cap at 5 files
                    'status': status,
                    'match_method': 'phase_fragment',
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
                has_stub = False
                for d in scan.declarations:
                    if d.name in matched_decl_names:
                        lean_files.append({
                            'path': d.file,
                            'declarations': [d.name],
                        })
                        if d.stub_kind is None:
                            has_genuine = True
                        else:
                            has_stub = True

                if has_genuine and has_stub:
                    status = "partial"
                elif has_genuine:
                    status = "proven"
                elif has_stub:
                    status = "stub"
                else:
                    status = "missing"
                matches[item.id] = {
                    'lean_files': lean_files[:3],
                    'status': status,
                    'match_method': 'fuzzy_name',
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
    matches = match_items_to_lean(items, scan)

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
            'lean_files': match_info['lean_files'],
        }
        if item.fragment:
            entry['fragment'] = item.fragment
        if item.section:
            entry['section'] = item.section
        index_items.append(entry)

    # Status counts
    status_counts = {}
    for item in index_items:
        s = item['status']
        status_counts[s] = status_counts.get(s, 0) + 1

    index = {
        'metadata': {
            'spec_file': 'docs/fdrs.md',
            'spec_lines': spec_lines,
            'generated_at': datetime.datetime.now().isoformat(),
            'total_items': len(index_items),
            'status_summary': status_counts,
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


if __name__ == "__main__":
    main()
