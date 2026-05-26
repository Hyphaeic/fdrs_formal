import FdrsFormal

/-!
# Declaration-level dependency extractor

Walks the compiled Lean environment and outputs declaration-level
dependency edges between FdrsFormal modules.

Run:   lake env lean scripts/lean_deps.lean 2>/dev/null
Output: TSV on stdout — source_file<TAB>source_decl<TAB>target_file<TAB>target_decl
-/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let entries := env.constants.fold (init := #[]) fun acc name cinfo =>
    if name.toString.startsWith "FdrsFormal." then
      acc.push (name, cinfo)
    else acc
  for (name, cinfo) in entries do
    let some srcIdx := env.const2ModIdx[name]? | continue
    let srcMod := modNames[srcIdx]!
    let srcStr := srcMod.toString
    unless srcStr.startsWith "FdrsFormal." do continue
    let srcPath := srcStr.replace "." "/" ++ ".lean"
    let srcDecl := name.toString
    let used := cinfo.type.getUsedConstants ++
      (match cinfo.value? with | some v => v.getUsedConstants | none => #[])
    for u in used do
      if u == name then continue
      let some tgtIdx := env.const2ModIdx[u]? | continue
      let tgtMod := modNames[tgtIdx]!
      let tgtStr := tgtMod.toString
      unless tgtStr.startsWith "FdrsFormal." do continue
      if srcStr == tgtStr then continue
      let tgtPath := tgtStr.replace "." "/" ++ ".lean"
      let tgtDecl := u.toString
      IO.println s!"{srcPath}\t{srcDecl}\t{tgtPath}\t{tgtDecl}"
