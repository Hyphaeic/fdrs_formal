#!/usr/bin/env python3
"""Parse docs/fdrs.md into structured mathematical items.

After global renumbering, items have the format:
  ### Definition 1 (finite horizon space)  [§2.1 · Phase 1, Fragment 1]
  **Definition 79** (Radix-induced ultrametric)  [§6.1.1 · Phase 6]
  **Proposition 91** (desc)  [P6.1 · Phase 6]
  ### Gate 1 (Scale projections)  [§G1 · Phase 2, Fragment 2]
  ### Example 1: Multi-Timeline RTOS Architecture  [§8.10.1 · Phase 8]
"""

import re
import json
import sys
from pathlib import Path
from dataclasses import dataclass, field, asdict
from typing import Optional


@dataclass
class SpecItem:
    id: str            # Global: definition_1, theorem_1, etc.
    type: str          # definition, theorem, proposition, lemma, corollary, example, gate
    global_num: int    # Monotonic number within type
    phase: int
    fragment: Optional[str]
    section: Optional[str]   # Original section number (§2.1, §6.1.1, etc.)
    title: str
    line: int
    raw_header: str

    def to_dict(self):
        d = asdict(self)
        return {k: v for k, v in d.items() if v is not None}


# Phase/Fragment boundary patterns
RE_PHASE_FRAGMENT = re.compile(
    r'^##\s+Phase\s+(\d+)\s*[—–-]\s*.+?,?\s*Fragment\s+(\S+)', re.IGNORECASE
)
RE_PHASE_HASH = re.compile(
    r'^#\s+Phase\s+(\d+):', re.IGNORECASE
)
RE_PHASE9 = re.compile(
    r'^##\s+Phase\s+9\s*[—–-]', re.IGNORECASE
)

# Annotation suffix pattern: [§2.1 · Phase 1, Fragment 1] or [P6.1 · Phase 6]
RE_ANNOTATION = re.compile(r'\[§?([^\]·]+?)(?:\s*·\s*Phase\s+(\d+)(?:,\s*Fragment\s+(\S+))?)?\]')

# Pattern 1: ### Definition N (title)  [annotation]
RE_HEADER_ITEM = re.compile(
    r'^###\s+(Definition|Theorem|Proposition|Lemma|Corollary)\s+'
    r'(\d+)\s*(?:\(([^)]*)\))?',
    re.IGNORECASE
)

# Pattern 2: ### Gate N (title)  [annotation]
RE_GATE = re.compile(
    r'^###\s+Gate\s+(\d+)\s*(?:\(([^)]*)\))?',
    re.IGNORECASE
)

# Pattern 3: ### Example N: title  [annotation]
RE_EXAMPLE_COLON = re.compile(
    r'^###\s+Example\s+(\d+)\s*:\s*(.*?)(?:\s*\[)',
    re.IGNORECASE
)
RE_EXAMPLE_COLON_SIMPLE = re.compile(
    r'^###\s+Example\s+(\d+)\s*:\s*(.*)',
    re.IGNORECASE
)

# Pattern 4: **Definition N** (title)  [annotation]  (Phases 6-8 bold inline)
RE_BOLD_ITEM = re.compile(
    r'^\*\*(Definition|Theorem|Proposition|Lemma|Corollary)\s+(\d+)\*\*\s*(?:\(([^)]*)\))?',
    re.IGNORECASE
)

# Pattern 5: **Proposition N.** (text)  (Phase 3 style, now renumbered to plain int)
RE_PHASE3_BOLD = re.compile(
    r'^\*\*(Proposition|Theorem|Corollary|Lemma|Definition)\s+(\d+)\s*'
    r'(?:\(([^)]*)\))?\s*[.*]?\*\*',
    re.IGNORECASE
)


def determine_phase_fragment(line: str, current_phase: int, current_fragment: Optional[str]):
    """Determine if a line changes the current phase/fragment context."""
    m = RE_PHASE_FRAGMENT.match(line)
    if m:
        return int(m.group(1)), m.group(2)
    m = RE_PHASE_HASH.match(line)
    if m:
        return int(m.group(1)), None
    m = RE_PHASE9.match(line)
    if m:
        return 9, None
    return current_phase, current_fragment


def extract_annotation(line: str) -> tuple[Optional[str], Optional[int], Optional[str]]:
    """Extract [§old_num · Phase N, Fragment F] annotation."""
    m = RE_ANNOTATION.search(line)
    if m:
        old_section = m.group(1).strip()
        phase = int(m.group(2)) if m.group(2) else None
        fragment = m.group(3)
        return old_section, phase, fragment
    return None, None, None


def parse_fdrs(fdrs_path: Path) -> list[SpecItem]:
    """Parse fdrs.md and return list of SpecItem objects."""
    lines = fdrs_path.read_text().splitlines()
    items: list[SpecItem] = []
    seen_ids: set[str] = set()

    current_phase = 1
    current_fragment: Optional[str] = "1"

    for lineno_0, line in enumerate(lines):
        lineno = lineno_0 + 1
        stripped = line.strip()
        if not stripped:
            continue

        # Update phase/fragment context
        new_phase, new_frag = determine_phase_fragment(stripped, current_phase, current_fragment)
        if new_phase != current_phase or new_frag != current_fragment:
            current_phase = new_phase
            current_fragment = new_frag
            continue

        # Extract annotation if present
        old_section, ann_phase, ann_fragment = extract_annotation(stripped)
        # Use annotation phase/fragment if available, else use current context
        item_phase = ann_phase if ann_phase is not None else current_phase
        item_fragment = ann_fragment if ann_fragment is not None else current_fragment

        # --- Pattern 1: ### Definition/Theorem/etc N (title) ---
        m = RE_HEADER_ITEM.match(stripped)
        if m:
            item_type = m.group(1).lower()
            global_num = int(m.group(2))
            title = m.group(3) or ""
            item_id = f"{item_type}_{global_num}"
            if item_id not in seen_ids:
                seen_ids.add(item_id)
                items.append(SpecItem(
                    id=item_id,
                    type=item_type,
                    global_num=global_num,
                    phase=item_phase,
                    fragment=item_fragment,
                    section=old_section,
                    title=title.strip(),
                    line=lineno,
                    raw_header=stripped,
                ))
            continue

        # --- Pattern 2: ### Gate N (title) ---
        m = RE_GATE.match(stripped)
        if m:
            global_num = int(m.group(1))
            title = m.group(2) or ""
            item_id = f"gate_{global_num}"
            if item_id not in seen_ids:
                seen_ids.add(item_id)
                items.append(SpecItem(
                    id=item_id,
                    type='gate',
                    global_num=global_num,
                    phase=item_phase,
                    fragment=item_fragment,
                    section=old_section,
                    title=title.strip(),
                    line=lineno,
                    raw_header=stripped,
                ))
            continue

        # --- Pattern 3: ### Example N: title  or  ### Example N (title) ---
        m = RE_EXAMPLE_COLON.match(stripped)
        if not m:
            m = RE_EXAMPLE_COLON_SIMPLE.match(stripped)
        if not m:
            # Also match ### Example N (title) [annotation]
            m_paren = re.match(r'^###\s+Example\s+(\d+)\s*\(([^)]*)\)', stripped, re.IGNORECASE)
            if m_paren:
                m = m_paren
        if m:
            global_num = int(m.group(1))
            title = m.group(2).strip()
            # Clean annotation from title
            title = re.sub(r'\s*\[§.*\]', '', title).strip()
            item_id = f"example_{global_num}"
            if item_id not in seen_ids:
                seen_ids.add(item_id)
                items.append(SpecItem(
                    id=item_id,
                    type='example',
                    global_num=global_num,
                    phase=item_phase,
                    fragment=item_fragment,
                    section=old_section,
                    title=title,
                    line=lineno,
                    raw_header=stripped,
                ))
            continue

        # --- Pattern 4: **Definition N** (title) for Phases 6-8 ---
        m = RE_BOLD_ITEM.match(stripped)
        if m:
            item_type = m.group(1).lower()
            global_num = int(m.group(2))
            title = m.group(3) or ""
            item_id = f"{item_type}_{global_num}"
            if item_id not in seen_ids:
                seen_ids.add(item_id)
                items.append(SpecItem(
                    id=item_id,
                    type=item_type,
                    global_num=global_num,
                    phase=item_phase,
                    fragment=item_fragment,
                    section=old_section,
                    title=title.strip(),
                    line=lineno,
                    raw_header=stripped,
                ))
            continue

        # --- Pattern 5: **Proposition N.** (Phase 3 bold, now renumbered) ---
        if current_phase in (3, 4):
            m = RE_PHASE3_BOLD.match(stripped)
            if m:
                item_type = m.group(1).lower()
                global_num = int(m.group(2))
                title = m.group(3) or ""
                item_id = f"{item_type}_{global_num}"
                if item_id not in seen_ids:
                    seen_ids.add(item_id)
                    items.append(SpecItem(
                        id=item_id,
                        type=item_type,
                        global_num=global_num,
                        phase=item_phase,
                        fragment=item_fragment,
                        section=old_section,
                        title=title.strip(),
                        line=lineno,
                        raw_header=stripped,
                    ))
                continue

    return items


def main():
    project_root = Path(__file__).resolve().parent.parent
    fdrs_path = project_root / "docs" / "fdrs.md"

    if not fdrs_path.exists():
        print(f"Error: {fdrs_path} not found", file=sys.stderr)
        sys.exit(1)

    items = parse_fdrs(fdrs_path)

    if "--json" in sys.argv:
        print(json.dumps([item.to_dict() for item in items], indent=2))
    else:
        by_type: dict[str, int] = {}
        by_phase: dict[int, int] = {}
        for item in items:
            by_type[item.type] = by_type.get(item.type, 0) + 1
            by_phase[item.phase] = by_phase.get(item.phase, 0) + 1

        print(f"Parsed {len(items)} items from {fdrs_path.name}")
        print(f"\nBy type:")
        for t in sorted(by_type):
            print(f"  {t:15s}: {by_type[t]:3d}")
        print(f"\nBy phase:")
        for p in sorted(by_phase):
            print(f"  Phase {p:2d}: {by_phase[p]:3d}")

    return items


if __name__ == "__main__":
    main()
