import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry8
import SymmetricSubgroupAsymptotics.GeneratedPair8.Installed8T1

/-! All original normal states of 8T1 enter their checked finite branch.
Character counting and the whole-family weighted sum remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T1
local instance : Group BinaryNormal8T1.Source := BinaryMenuCayley8T1.group
abbrev Original := BinaryPairInstalled8T1.Original

/-- No semantic acceptance or normal-enumeration premise is required. -/
theorem finiteEntryCoverage (N : Subgroup Original) [N.Normal] : BinaryFiniteEntry8 Original N := by
  rcases BinaryPairInstalled8T1.normal_coverage N with ⟨j,rfl⟩|⟨i,hi,he⟩
  · exact Or.inl ⟨{
      pairCount := 4
      frame := BinaryPairInstalled8T1.frame
      generatorCount := 1
      generators := BinaryPairInstalled8T1.generators
      generators_full := BinaryPairInstalled8T1.generators_full
      localCertificate := BinaryPairInstalled8T1.physicalCertificates j
      physical_width := BinaryPairInstalled8T1.physical_width j }⟩
  · fin_cases i
    · exact False.elim ((by decide +kernel : ¬(0 : Fin 4)∈BinaryPairInstalled8T1.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(1 : Fin 4)∈BinaryPairInstalled8T1.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(2 : Fin 4)∈BinaryPairInstalled8T1.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(3 : Fin 4)∈BinaryPairInstalled8T1.residualIndices) hi)
end SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T1
