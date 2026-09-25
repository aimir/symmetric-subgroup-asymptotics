import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry8
import SymmetricSubgroupAsymptotics.GeneratedPair8.Installed8T8

/-! All original normal states of 8T8 enter their checked finite branch.
Character counting and the whole-family weighted sum remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T8
local instance : Group BinaryNormal8T8.Source := BinaryMenuCayley8T8.group
abbrev Original := BinaryPairInstalled8T8.Original

/-- No semantic acceptance or normal-enumeration premise is required. -/
theorem finiteEntryCoverage (N : Subgroup Original) [N.Normal] : BinaryFiniteEntry8 Original N := by
  rcases BinaryPairInstalled8T8.normal_coverage N with ⟨j,rfl⟩|⟨i,hi,he⟩
  · exact Or.inl ⟨{
      pairCount := 4
      frame := BinaryPairInstalled8T8.frame
      generatorCount := 2
      generators := BinaryPairInstalled8T8.generators
      generators_full := BinaryPairInstalled8T8.generators_full
      localCertificate := BinaryPairInstalled8T8.physicalCertificates j
      physical_width := BinaryPairInstalled8T8.physical_width j }⟩
  · fin_cases i
    · exact False.elim ((by decide +kernel : ¬(0 : Fin 7)∈BinaryPairInstalled8T8.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(1 : Fin 7)∈BinaryPairInstalled8T8.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(2 : Fin 7)∈BinaryPairInstalled8T8.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(3 : Fin 7)∈BinaryPairInstalled8T8.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(4 : Fin 7)∈BinaryPairInstalled8T8.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(5 : Fin 7)∈BinaryPairInstalled8T8.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(6 : Fin 7)∈BinaryPairInstalled8T8.residualIndices) hi)
end SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T8
