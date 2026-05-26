#!/usr/bin/env python3
"""Scan all .lean files under FdrsFormal/ and extract declarations, axioms, sorries, imports, and fdrs.md references."""

import re
import json
import sys
from pathlib import Path
from dataclasses import dataclass, field, asdict
from typing import Optional


@dataclass
class AxiomDecl:
    name: str
    type_sig: str
    file: str
    line: int
    is_true_stub: bool  # axiom whose type is or contains `True`

    def to_dict(self):
        return asdict(self)


@dataclass
class SorryOccurrence:
    file: str
    line: int
    context: str  # surrounding line content

    def to_dict(self):
        return asdict(self)


@dataclass
class Declaration:
    kind: str  # theorem, def, lemma, instance, etc.
    name: str
    file: str
    line: int
    stub_kind: Optional[str] = None  # None=genuine, "true_trivial", "prop_true", "zero_impl"

    def to_dict(self):
        d = asdict(self)
        if d['stub_kind'] is None:
            del d['stub_kind']
        return d


@dataclass
class NotationDecl:
    symbol: str
    expansion: str
    file: str
    line: int
    scoped: bool
    precedence: Optional[int] = None  # For infixl/infixr/prefix/postfix
    is_local: bool = False  # For local notations

    def to_dict(self):
        d = asdict(self)
        # Remove None values for cleaner output
        return {k: v for k, v in d.items() if v is not None and not (k == 'is_local' and not v)}


@dataclass
class FdrsRef:
    file: str
    line: int
    text: str  # the matched reference text

    def to_dict(self):
        return asdict(self)


@dataclass
class FileImport:
    source_file: str
    imported_module: str

    def to_dict(self):
        return asdict(self)


@dataclass
class LeanScanResult:
    total_files: int
    axioms: list[AxiomDecl]
    sorries: list[SorryOccurrence]
    declarations: list[Declaration]
    notations: list[NotationDecl]
    fdrs_refs: list[FdrsRef]
    imports: list[FileImport]

    def to_dict(self):
        stubs = [d for d in self.declarations if d.stub_kind is not None]
        return {
            'total_files': self.total_files,
            'total_axioms': len(self.axioms),
            'axioms_true': sum(1 for a in self.axioms if a.is_true_stub),
            'total_sorries': len(self.sorries),
            'total_theorems': sum(1 for d in self.declarations if d.kind == 'theorem'),
            'total_defs': sum(1 for d in self.declarations if d.kind == 'def'),
            'total_lemmas': sum(1 for d in self.declarations if d.kind == 'lemma'),
            'total_stubs': len(stubs),
            'stubs_by_kind': {
                'true_trivial': sum(1 for d in stubs if d.stub_kind == 'true_trivial'),
                'prop_true': sum(1 for d in stubs if d.stub_kind == 'prop_true'),
                'zero_impl': sum(1 for d in stubs if d.stub_kind == 'zero_impl'),
            },
            'total_notations': len(self.notations),
            'axioms': [a.to_dict() for a in self.axioms],
            'sorries': [s.to_dict() for s in self.sorries],
            'sorry_files': self._sorry_files(),
            'stubs': [d.to_dict() for d in stubs],
            'notations': [n.to_dict() for n in self.notations],
            'fdrs_refs': [r.to_dict() for r in self.fdrs_refs],
            'imports': [i.to_dict() for i in self.imports],
        }

    def _sorry_files(self) -> list[dict]:
        """Group sorries by file."""
        by_file: dict[str, list[int]] = {}
        for s in self.sorries:
            by_file.setdefault(s.file, []).append(s.line)
        return [{'file': f, 'lines': lines} for f, lines in sorted(by_file.items())]


# Patterns
RE_AXIOM = re.compile(r'^axiom\s+(\S+)\s*(.*)')
RE_SORRY = re.compile(r'\bsorry\b')
RE_DECL = re.compile(r'^(theorem|def|lemma|noncomputable def|noncomputable instance|instance|abbrev|structure|class|inductive)\s+(\S+)')
RE_NOTATION = re.compile(r'^(scoped\s+)?notation\b(.+)')
# Infix/prefix/postfix notations: (local)? (infixl|infixr|prefix|postfix):precedence "symbol" => expansion
RE_INFIX = re.compile(r'^(local\s+)?(infixl|infixr|prefix|postfix)\s*:\s*(\d+)\s+"([^"]+)"\s*=>\s*(.+)')
RE_IMPORT = re.compile(r'^import\s+(FdrsFormal\S*)')
RE_FDRS_REF = re.compile(r'fdrs\.md[^"]*?(?:lines?\s+\d+[\s–-]*\d*|Phase\s+\d+[^"]*)', re.IGNORECASE)
RE_FDRS_REF_SIMPLE = re.compile(r'fdrs\.md', re.IGNORECASE)
# For extracting line ranges
RE_FDRS_LINES = re.compile(r'lines?\s+(\d+)\s*[-–to]+\s*(\d+)', re.IGNORECASE)

# True-stub detection
RE_TRUE_TYPE = re.compile(r':\s*(?:.*→\s*)?True\b|:\s*(?:.*→\s*)?Decidable\s+True')

# Top-level constructs that signal end of a declaration body
_DECL_STOP_PREFIXES = (
    'axiom ', 'theorem ', 'def ', 'lemma ', 'noncomputable ',
    'instance ', 'abbrev ', 'structure ', 'class ', 'inductive ',
    'namespace ', 'end ', 'section ', '#', 'open ', 'variable ',
    'attribute ', 'import ', '@[',
)


def _collect_decl_parts(lines: list[str], start_idx: int) -> Optional[tuple[str, str]]:
    """Collect type and body parts of a declaration starting at start_idx.

    Returns (type_text, body_text) or None if no := found within 30 lines.
    """
    collected = []
    found_assign = False
    body_lines_count = 0

    for j in range(start_idx, min(start_idx + 30, len(lines))):
        stripped = lines[j].strip()

        # Stop at next top-level construct (not on first line)
        if j > start_idx and any(stripped.startswith(p) for p in _DECL_STOP_PREFIXES):
            break

        # After := found, stop at blank line or block comment start
        if found_assign and (stripped == '' or stripped.startswith('/-')):
            break

        # Remove inline comments for analysis
        if '--' in stripped:
            code = stripped[:stripped.index('--')].rstrip()
        else:
            code = stripped

        collected.append(code)

        if ':=' in code:
            found_assign = True
        elif found_assign:
            body_lines_count += 1
            if body_lines_count >= 3:
                break

    text = ' '.join(collected)
    idx = text.find(':=')
    if idx == -1:
        return None

    return (text[:idx].strip(), text[idx + 2:].strip())


def _detect_stub_kind(lines: list[str], start_idx: int, kind: str) -> Optional[str]:
    """Detect if a declaration starting at start_idx is a stub.

    Only checks theorem/lemma/def/abbrev — instances, structures, classes,
    and inductives are excluded (they're infrastructure, not spec item stubs).

    Returns:
        None for genuine declarations
        "true_trivial" for `: True := trivial` or `: True := by trivial`
        "prop_true" for `: Prop := True`
        "zero_impl" for `:= fun _ => 0`
    """
    if kind not in ('theorem', 'lemma', 'def', 'abbrev'):
        return None

    parts = _collect_decl_parts(lines, start_idx)
    if parts is None:
        return None

    type_part, body_raw = parts

    # Normalize body whitespace
    body = ' '.join(body_raw.split())

    # true_trivial: type ends with `True`, body is `trivial` or `by trivial`
    if re.search(r'True\s*$', type_part):
        if body in ('trivial', 'by trivial'):
            return "true_trivial"

    # prop_true: type ends with `Prop`, body is `True`
    if re.search(r'Prop\s*$', type_part):
        if body == 'True':
            return "prop_true"

    # zero_impl: body is `fun <args> => 0`
    if re.match(r'^fun[\s\w_]+=> 0$', body):
        return "zero_impl"

    return None


def scan_file(filepath: Path, rel_path: str) -> tuple[
    list[AxiomDecl], list[SorryOccurrence], list[Declaration],
    list[NotationDecl], list[FdrsRef], list[FileImport]
]:
    axioms = []
    sorries = []
    decls = []
    notations = []
    fdrs_refs = []
    imports = []

    try:
        lines = filepath.read_text().splitlines()
    except Exception:
        return axioms, sorries, decls, notations, fdrs_refs, imports

    in_block_comment = False

    for lineno_0, line in enumerate(lines):
        lineno = lineno_0 + 1
        stripped = line.strip()

        # Track block comments
        if '/-' in line and '-/' not in line:
            in_block_comment = True
        if '-/' in line:
            in_block_comment = False

        # Imports (always at top of file, outside comments)
        m = RE_IMPORT.match(stripped)
        if m:
            imports.append(FileImport(source_file=rel_path, imported_module=m.group(1)))
            continue

        # fdrs.md references (can be in comments or docstrings)
        if 'fdrs.md' in line.lower() or 'fdrs.md' in line:
            m = RE_FDRS_REF.search(line)
            if m:
                fdrs_refs.append(FdrsRef(file=rel_path, line=lineno, text=m.group(0)))
            elif RE_FDRS_REF_SIMPLE.search(line):
                fdrs_refs.append(FdrsRef(file=rel_path, line=lineno, text=line.strip()))

        # Skip comment-only lines for declaration scanning
        if stripped.startswith('--') or in_block_comment:
            # But still check for sorry in actual code
            continue

        # Axioms
        m = RE_AXIOM.match(stripped)
        if m:
            name = m.group(1)
            rest = m.group(2)
            # Read continuation lines for type signature
            type_sig = rest
            j = lineno_0 + 1
            while j < len(lines) and not lines[j].strip().startswith(('axiom', 'theorem', 'def', 'lemma', 'import', '--', '/-', 'noncomputable', 'instance', 'structure', 'class', 'inductive', 'abbrev', 'section', 'namespace', 'end', 'open', 'variable', '#')):
                type_sig += ' ' + lines[j].strip()
                if lines[j].strip() == '' or ':=' in lines[j]:
                    break
                j += 1

            is_true = bool(RE_TRUE_TYPE.search(type_sig))
            axioms.append(AxiomDecl(
                name=name,
                type_sig=type_sig.strip()[:200],
                file=rel_path,
                line=lineno,
                is_true_stub=is_true,
            ))
            continue

        # Sorry
        if RE_SORRY.search(stripped) and not stripped.startswith('--'):
            # Make sure it's not in a string or comment suffix
            # Simple heuristic: check it's not after --
            code_part = stripped.split('--')[0] if '--' in stripped else stripped
            if 'sorry' in code_part:
                context_lines = []
                for delta in range(-2, 3):
                    idx = lineno_0 + delta
                    if 0 <= idx < len(lines):
                        context_lines.append(lines[idx].rstrip())
                sorries.append(SorryOccurrence(
                    file=rel_path,
                    line=lineno,
                    context='\n'.join(context_lines),
                ))

        # Declarations
        m = RE_DECL.match(stripped)
        if m:
            kind = m.group(1).replace('noncomputable ', '')
            name = m.group(2)
            stub_kind = _detect_stub_kind(lines, lineno_0, kind)
            decls.append(Declaration(kind=kind, name=name, file=rel_path, line=lineno, stub_kind=stub_kind))
            continue

        # Infix/prefix/postfix notations
        m = RE_INFIX.match(stripped)
        if m:
            is_local = bool(m.group(1))
            notation_type = m.group(2)  # infixl, infixr, prefix, postfix
            precedence = int(m.group(3))
            symbol = m.group(4).strip()
            expansion = m.group(5).strip()

            # Format symbol with notation type for clarity
            symbol_display = f'{symbol} ({notation_type}:{precedence})'
            if is_local:
                symbol_display = f'{symbol} (local {notation_type}:{precedence})'

            notations.append(NotationDecl(
                symbol=symbol_display,
                expansion=expansion,
                file=rel_path,
                line=lineno,
                scoped=False,  # infix notations are not "scoped" in the same way
                precedence=precedence,
                is_local=is_local,
            ))
            continue

        # Regular notations
        m = RE_NOTATION.match(stripped)
        if m:
            is_scoped = bool(m.group(1))
            rest = m.group(2).strip()
            # Try to split on =>
            parts = rest.split('=>', 1)
            symbol = parts[0].strip().strip('"').strip() if parts else rest
            expansion = parts[1].strip() if len(parts) > 1 else ""
            notations.append(NotationDecl(
                symbol=symbol,
                expansion=expansion,
                file=rel_path,
                line=lineno,
                scoped=is_scoped,
            ))

    return axioms, sorries, decls, notations, fdrs_refs, imports


def scan_project(project_root: Path) -> LeanScanResult:
    """Scan all .lean files under FdrsFormal/."""
    lean_dir = project_root / "FdrsFormal"
    lean_files = sorted(lean_dir.rglob("*.lean"))

    all_axioms = []
    all_sorries = []
    all_decls = []
    all_notations = []
    all_fdrs_refs = []
    all_imports = []

    for fp in lean_files:
        rel = str(fp.relative_to(project_root))
        axioms, sorries, decls, notations, refs, imports = scan_file(fp, rel)
        all_axioms.extend(axioms)
        all_sorries.extend(sorries)
        all_decls.extend(decls)
        all_notations.extend(notations)
        all_fdrs_refs.extend(refs)
        all_imports.extend(imports)

    return LeanScanResult(
        total_files=len(lean_files),
        axioms=all_axioms,
        sorries=all_sorries,
        declarations=all_decls,
        notations=all_notations,
        fdrs_refs=all_fdrs_refs,
        imports=all_imports,
    )


def main():
    project_root = Path(__file__).resolve().parent.parent
    result = scan_project(project_root)

    if "--json" in sys.argv:
        print(json.dumps(result.to_dict(), indent=2))
    else:
        stubs = [d for d in result.declarations if d.stub_kind is not None]
        genuine = [d for d in result.declarations if d.stub_kind is None]
        print(f"Scanned {result.total_files} .lean files")
        print(f"  Axioms:    {len(result.axioms)} ({sum(1 for a in result.axioms if a.is_true_stub)} True stubs)")
        print(f"  Sorries:   {len(result.sorries)}")
        print(f"  Theorems:  {sum(1 for d in result.declarations if d.kind == 'theorem')}")
        print(f"  Defs:      {sum(1 for d in result.declarations if d.kind == 'def')}")
        print(f"  Lemmas:    {sum(1 for d in result.declarations if d.kind == 'lemma')}")
        print(f"  Genuine:   {len(genuine)}")
        print(f"  Stubs:     {len(stubs)} ("
              f"{sum(1 for d in stubs if d.stub_kind == 'true_trivial')} True:=trivial, "
              f"{sum(1 for d in stubs if d.stub_kind == 'prop_true')} Prop:=True, "
              f"{sum(1 for d in stubs if d.stub_kind == 'zero_impl')} fun_=>_0)")
        print(f"  Notations: {len(result.notations)}")
        print(f"  fdrs.md refs: {len(result.fdrs_refs)}")
        print(f"  Imports:   {len(result.imports)}")

        if result.sorries:
            print(f"\nSorry locations:")
            for s in result.sorries:
                print(f"  {s.file}:{s.line}")

        if stubs and "--stubs" in sys.argv:
            print(f"\nStub declarations:")
            for d in stubs:
                print(f"  {d.file}:{d.line}  {d.kind} {d.name}  [{d.stub_kind}]")

    return result


if __name__ == "__main__":
    main()
