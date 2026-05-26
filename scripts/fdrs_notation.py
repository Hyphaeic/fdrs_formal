#!/usr/bin/env python3
"""Generate docs/notation.md from Lean notation declarations."""

import sys
from pathlib import Path

# Import scanner
sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_scan import scan_project


def generate_notation_md(project_root: Path) -> str:
    """Generate notation.md content from scanned notations."""
    scan = scan_project(project_root)
    notations = sorted(scan.notations, key=lambda n: n.symbol.lower())

    lines = [
        "# FDRS Notation Reference",
        "",
        "Auto-generated from Lean source files.",
        "",
        "## Lean Notations",
        "",
        "| Symbol | Expansion | File | Line | Scoped |",
        "|--------|-----------|------|------|--------|",
    ]

    for n in notations:
        symbol = f'`{n.symbol}`'
        expansion = f'`{n.expansion}`'
        file_short = n.file
        scoped_mark = '✓' if n.scoped else ''

        lines.append(f"| {symbol} | {expansion} | {file_short} | {n.line} | {scoped_mark} |")

    lines.extend([
        "",
        "## Key Mathematical Symbols",
        "",
        "| Symbol | Meaning | fdrs.md Ref |",
        "|--------|---------|-------------|",
        "| b_i | Radix at position i | Phase 1, Section 1 |",
        "| D_i | Digit alphabet {0,...,b_i-1} | Phase 1, Section 1 |",
        "| B_m | Cumulative radix product | Phase 1, Section 1 |",
        "| R^(k) | Finite mixed-radix space | Def 1 |",
        "| R^(∞)_fin | Direct-limit space | Def 3 |",
        "| R̂ | Completed mixed-radix space | Def 7 |",
        "| dec | Decoding map (ℛ → ℕ) | Def 2, 4 |",
        "| enc | Encoding map (ℕ → ℛ) | Def 2, 4 |",
        "| T(x) | Tick operator (successor) | Def 5, 6 |",
        "| ⊕ | Addition on ℛ | Def 14, Prop 10 |",
        "| ⊖ | Subtraction on ℛ (partial) | Def 13, Prop 9 |",
        "| pred | Predecessor on ℛ | Def 12 |",
        "| δ(x,y) | Ultrametric distance | Def 9, Prop 3 |",
        "| U(s) | Cylinder set at prefix s | Def 8 |",
        "| π_L | Prefix projection to depth L | Def 10 |",
        "| r_L | Prefix residue / value | Def 11 |",
        "| P_L | Block projection operator | Def 22, Prop 16 |",
        "| Δ_L | Detail operator | Def 23, Prop 18 |",
        "| 𝕋(V) | Mixed-radix tensor space | Phase 2 |",
        "| ε | Dirichlet identity | Phase 3 |",
        "| μ | Möbius function | Phase 3 |",
        "| μ² | Squarefree indicator | Phase 3, Prop 40 |",
        "| ⋆ | Dirichlet convolution | Phase 3 |",
        "| v_p | p-adic valuation | Phase 3 |",
        "| ω | Radix function (variable) | Phase 5, Def 57 |",
        "| β_ω(s) | Odometer weight | Phase 5, Def 75-76 |",
        "| δ_ω | Radix-induced ultrametric | Phase 6, Def 79 |",
        "| Ω | Extended radix oracle | Phase 7, Def 85 |",
        "| 𝒢 | Timeline graph | Phase 8, Def 108 |",
        "| ρ | Routing function | Phase 8, Def 112 |",
        "",
    ])

    return '\n'.join(lines)


def main():
    project_root = Path(__file__).resolve().parent.parent
    output_path = project_root / "docs" / "notation.md"

    content = generate_notation_md(project_root)
    output_path.write_text(content)

    print(f"Generated {output_path}")
    print(f"  Total notations: {content.count('|') // 6 - 2}")  # Rough count


if __name__ == "__main__":
    main()
