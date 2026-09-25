import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry8
import SymmetricSubgroupAsymptotics.GeneratedPair8.Installed8T7
import SymmetricSubgroupAsymptotics.GeneratedCharacter8.Characters8T7

/-! All original normal states of 8T7 enter their checked finite branch.
Character counting and the whole-family weighted sum remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T7
local instance : Group BinaryNormal8T7.Source := BinaryMenuCayley8T7.group
abbrev Original := BinaryPairInstalled8T7.Original

/-- No semantic acceptance or normal-enumeration premise is required. -/
theorem finiteEntryCoverage (N : Subgroup Original) [N.Normal] : BinaryFiniteEntry8 Original N := by
  rcases BinaryPairInstalled8T7.normal_coverage N with ⟨j,rfl⟩|⟨i,hi,he⟩
  · exact Or.inl ⟨{
      pairCount := 4
      frame := BinaryPairInstalled8T7.frame
      generatorCount := 2
      generators := BinaryPairInstalled8T7.generators
      generators_full := BinaryPairInstalled8T7.generators_full
      localCertificate := BinaryPairInstalled8T7.physicalCertificates j
      physical_width := BinaryPairInstalled8T7.physical_width j }⟩
  · fin_cases i
    · cases he
      exact Or.inr (Or.inl ⟨BinaryNormalCharacters8T7.N0.physicalCriterion⟩)
    · exact False.elim ((by decide +kernel : ¬(1 : Fin 9)∈BinaryPairInstalled8T7.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(2 : Fin 9)∈BinaryPairInstalled8T7.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(3 : Fin 9)∈BinaryPairInstalled8T7.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(4 : Fin 9)∈BinaryPairInstalled8T7.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(5 : Fin 9)∈BinaryPairInstalled8T7.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(6 : Fin 9)∈BinaryPairInstalled8T7.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(7 : Fin 9)∈BinaryPairInstalled8T7.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(8 : Fin 9)∈BinaryPairInstalled8T7.residualIndices) hi)
end SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T7
