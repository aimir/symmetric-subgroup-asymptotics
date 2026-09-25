import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry8
import SymmetricSubgroupAsymptotics.GeneratedPair8.Installed8T17
import SymmetricSubgroupAsymptotics.GeneratedCharacter8.Characters8T17

/-! All original normal states of 8T17 enter their checked finite branch.
Character counting and the whole-family weighted sum remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T17
local instance : Group BinaryNormal8T17.Source := BinaryMenuCayley8T17.group
abbrev Original := BinaryPairInstalled8T17.Original

/-- No semantic acceptance or normal-enumeration premise is required. -/
theorem finiteEntryCoverage (N : Subgroup Original) [N.Normal] : BinaryFiniteEntry8 Original N := by
  rcases BinaryPairInstalled8T17.normal_coverage N with ⟨j,rfl⟩|⟨i,hi,he⟩
  · exact Or.inl ⟨{
      pairCount := 4
      frame := BinaryPairInstalled8T17.frame
      generatorCount := 2
      generators := BinaryPairInstalled8T17.generators
      generators_full := BinaryPairInstalled8T17.generators_full
      localCertificate := BinaryPairInstalled8T17.physicalCertificates j
      physical_width := BinaryPairInstalled8T17.physical_width j }⟩
  · fin_cases i
    · cases he
      exact Or.inr (Or.inl ⟨BinaryNormalCharacters8T17.N0.physicalCriterion⟩)
    · exact False.elim ((by decide +kernel : ¬(1 : Fin 12)∈BinaryPairInstalled8T17.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(2 : Fin 12)∈BinaryPairInstalled8T17.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(3 : Fin 12)∈BinaryPairInstalled8T17.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(4 : Fin 12)∈BinaryPairInstalled8T17.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(5 : Fin 12)∈BinaryPairInstalled8T17.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(6 : Fin 12)∈BinaryPairInstalled8T17.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(7 : Fin 12)∈BinaryPairInstalled8T17.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(8 : Fin 12)∈BinaryPairInstalled8T17.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(9 : Fin 12)∈BinaryPairInstalled8T17.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(10 : Fin 12)∈BinaryPairInstalled8T17.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(11 : Fin 12)∈BinaryPairInstalled8T17.residualIndices) hi)
end SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T17
