import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry8
import SymmetricSubgroupAsymptotics.GeneratedPair8.Installed8T11
import SymmetricSubgroupAsymptotics.GeneratedCharacter8.Characters8T11

/-! All original normal states of 8T11 enter their checked finite branch.
Character counting and the whole-family weighted sum remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T11
local instance : Group BinaryNormal8T11.Source := BinaryMenuCayley8T11.group
abbrev Original := BinaryPairInstalled8T11.Original

/-- No semantic acceptance or normal-enumeration premise is required. -/
theorem finiteEntryCoverage (N : Subgroup Original) [N.Normal] : BinaryFiniteEntry8 Original N := by
  rcases BinaryPairInstalled8T11.normal_coverage N with ⟨j,rfl⟩|⟨i,hi,he⟩
  · exact Or.inl ⟨{
      pairCount := 4
      frame := BinaryPairInstalled8T11.frame
      generatorCount := 3
      generators := BinaryPairInstalled8T11.generators
      generators_full := BinaryPairInstalled8T11.generators_full
      localCertificate := BinaryPairInstalled8T11.physicalCertificates j
      physical_width := BinaryPairInstalled8T11.physical_width j }⟩
  · fin_cases i
    · cases he
      exact Or.inr (Or.inl ⟨BinaryNormalCharacters8T11.N0.physicalCriterion⟩)
    · exact False.elim ((by decide +kernel : ¬(1 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(2 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(3 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(4 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(5 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(6 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(7 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(8 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(9 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(10 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(11 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(12 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(13 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(14 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(15 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(16 : Fin 17)∈BinaryPairInstalled8T11.residualIndices) hi)
end SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T11
