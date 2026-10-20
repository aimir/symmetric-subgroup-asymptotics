import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1098SectionCheck000

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairBinding16T1098
local instance pilotSectionsGroup : Group SourceTop := BinaryTopSource046.group

theorem section_checked : ∀ q, BinaryPairFrame.Preserves frame
    (sectionMap q : Equiv.Perm (Fin 16)) (BinaryTopSource046.originalEquiv q : Equiv.Perm (Fin 8)) := by
  intro q
  exact section_checked000 q (Nat.zero_le _) q.index.isLt


theorem section_right (q : SourceTop) : sourceMap (sectionMap q)=q := by
  apply topEquiv.injective
  change topEquiv (topEquiv.symm (physicalFrame.top.rangeRestrict (sectionMap q)))=_
  rw [topEquiv.apply_symm_apply]
  apply Subtype.ext
  exact BinaryPairFrame.preserves_unique frame (physicalFrame.intertwine (sectionMap q)) (section_checked q)
theorem section_identity : sectionMap 1=1 := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryPairBinding16T1098
