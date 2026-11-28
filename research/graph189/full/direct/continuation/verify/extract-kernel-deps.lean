import Lean

/- Diagnostic for the single-file packager. Prepend imports for
the modules under examination and set GRAPH189_ROOT in the environment. -/
open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let root := (← IO.getEnv "GRAPH189_ROOT").getD "Graph189ModerateComplete.moderate"
  let rootName := root.toName
  unless env.contains rootName do throwError "missing declaration {rootName}"
  let mut todo := [rootName]
  let mut seen : NameSet := {}
  let mut output := ""
  while let name :: rest := todo do
    todo := rest
    if seen.contains name then continue
    seen := seen.insert name
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.toString.startsWith "Graph189" do continue
    let userName := privateToUserName name
    if mod == `Graph189ModerateSplit then continue
    if mod == `Graph189ParentFocused then
      if userName.toString.startsWith "OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2." ||
         userName.toString.startsWith "OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1." then continue
    let some info := env.find? name | throwError "missing imported definition {name}"
    let range ← findDeclarationRanges? name
    let line := (range.map (·.selectionRange.pos.line)).getD 0
    let body := info.value? (allowOpaque := true)
    output := output ++ s!"{mod}\t{userName}\t{line}\t{body.isSome}\n"
    for next in info.getUsedConstantsAsSet do
      todo := next :: todo
  let dest := (← IO.getEnv "GRAPH189_DEPENDENCIES").getD "moderate-dependencies.tsv"
  IO.FS.writeFile dest output
