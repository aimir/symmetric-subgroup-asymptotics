import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1098SectionData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairBinding16T1098
local instance pilotSectionCheck000Group : Group SourceTop := BinaryTopSource046.group

theorem section_checked000 : ∀ q : SourceTop,
    0≤q.index.val → q.index.val<16 → BinaryPairFrame.Preserves frame
    (sectionMap q : Equiv.Perm (Fin 16))
    (BinaryTopSource046.originalEquiv q : Equiv.Perm (Fin 8)) := by
  unfold BinaryPairFrame.Preserves
  simp only [← BinaryKernelAxes077.rowPermutation_eq_original]
  decide +kernel
end SymmetricSubgroupAsymptotics.BinaryPairBinding16T1098
