import VariationalAnalysis
open Lean Elab Command

/-- Lists every declaration of the `VariationalAnalysis` modules whose proof depends on an axiom
other than `propext`, `Classical.choice`, `Quot.sound` (e.g. `sorryAx`). -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total : Nat := 0
  let mut bad : Array (Name × List Name) := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`VariationalAnalysis).isPrefixOf mod do continue
    if n.isInternal then continue
    total := total + 1
    let axs ← liftCoreM <| Lean.collectAxioms n
    let extra := axs.toList.filter (fun a => !std.contains a)
    unless extra.isEmpty do bad := bad.push (n, extra)
  logInfo m!"declarations checked: {total}; with non-standard axioms: {bad.size}"
  for (n, a) in bad do logInfo m!"{n}: {a}"

#audit_axioms
