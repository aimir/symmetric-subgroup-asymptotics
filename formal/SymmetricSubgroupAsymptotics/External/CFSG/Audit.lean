import SymmetricSubgroupAsymptotics.External.CFSG.Classification
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! A build-time audit, not a mathematical assumption. Inspect every declaration
originating in a CFSG module, including generated declarations and instances.
Reject all axioms except Lean's three standard logical foundations, transitively.
The audit log is emitted to the external checker log directory. -/

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | none => names
    | some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      if modName == `SymmetricSubgroupAsymptotics.External.CFSG ||
          (`SymmetricSubgroupAsymptotics.External.CFSG).isPrefixOf modName
        then names.push name else names
  if names.isEmpty then throwError "No CFSG declarations found; audit would be vacuous"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names.qsort Name.quickLt do
    if (env.find? name).any (·.isAxiom) then
      throwError "Project declares an axiom: {name}"
    if (env.find? name).any (·.isUnsafe) then
      throwError "Project declares unsafe code: {name}"
    let axioms ← Lean.collectAxioms name
    for a in axioms do
      unless allowed.contains a do
        throwError "Unexpected axiom {a} in {name}"
    logInfo m!"AXIOMS {name}: {axioms}"
  logInfo m!"PASS: audited {names.size} project declarations; only propext, Classical.choice, Quot.sound permitted"

#print axioms CFSG.CFSGClassification
#print axioms CFSG.CFSGClassification.classify
#print axioms CFSG.Index.Model
#print axioms CFSG.Index.instGroupModel
