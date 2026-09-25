import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry8
import SymmetricSubgroupAsymptotics.GeneratedPair8.Installed8T30
import SymmetricSubgroupAsymptotics.GeneratedCharacter8.Characters8T30

/-! All original normal states of 8T30 enter their checked finite branch.
Character counting and the whole-family weighted sum remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T30
local instance : Group BinaryNormal8T30.Source := BinaryMenuCayley8T30.group
abbrev Original := BinaryPairInstalled8T30.Original

/-- No semantic acceptance or normal-enumeration premise is required. -/
theorem finiteEntryCoverage (N : Subgroup Original) [N.Normal] : BinaryFiniteEntry8 Original N := by
  rcases BinaryPairInstalled8T30.normal_coverage N with ⟨j,rfl⟩|⟨i,hi,he⟩
  · exact Or.inl ⟨{
      pairCount := 4
      frame := BinaryPairInstalled8T30.frame
      generatorCount := 3
      generators := BinaryPairInstalled8T30.generators
      generators_full := BinaryPairInstalled8T30.generators_full
      localCertificate := BinaryPairInstalled8T30.physicalCertificates j
      physical_width := BinaryPairInstalled8T30.physical_width j }⟩
  · fin_cases i
    · cases he
      exact Or.inr (Or.inl ⟨BinaryNormalCharacters8T30.N0.physicalCriterion⟩)
    · cases he
      exact Or.inr (Or.inl ⟨BinaryNormalCharacters8T30.N1.physicalCriterion⟩)
    · exact False.elim ((by decide +kernel : ¬(2 : Fin 13)∈BinaryPairInstalled8T30.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(3 : Fin 13)∈BinaryPairInstalled8T30.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(4 : Fin 13)∈BinaryPairInstalled8T30.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(5 : Fin 13)∈BinaryPairInstalled8T30.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(6 : Fin 13)∈BinaryPairInstalled8T30.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(7 : Fin 13)∈BinaryPairInstalled8T30.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(8 : Fin 13)∈BinaryPairInstalled8T30.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(9 : Fin 13)∈BinaryPairInstalled8T30.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(10 : Fin 13)∈BinaryPairInstalled8T30.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(11 : Fin 13)∈BinaryPairInstalled8T30.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(12 : Fin 13)∈BinaryPairInstalled8T30.residualIndices) hi)
end SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T30
