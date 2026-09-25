import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry8
import SymmetricSubgroupAsymptotics.GeneratedPair8.Installed8T21
import SymmetricSubgroupAsymptotics.GeneratedCharacter8.Characters8T21

/-! All original normal states of 8T21 enter their checked finite branch.
Character counting and the whole-family weighted sum remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T21
local instance : Group BinaryNormal8T21.Source := BinaryMenuCayley8T21.group
abbrev Original := BinaryPairInstalled8T21.Original

/-- No semantic acceptance or normal-enumeration premise is required. -/
theorem finiteEntryCoverage (N : Subgroup Original) [N.Normal] : BinaryFiniteEntry8 Original N := by
  rcases BinaryPairInstalled8T21.normal_coverage N with ⟨j,rfl⟩|⟨i,hi,he⟩
  · exact Or.inl ⟨{
      pairCount := 4
      frame := BinaryPairInstalled8T21.frame
      generatorCount := 3
      generators := BinaryPairInstalled8T21.generators
      generators_full := BinaryPairInstalled8T21.generators_full
      localCertificate := BinaryPairInstalled8T21.physicalCertificates j
      physical_width := BinaryPairInstalled8T21.physical_width j }⟩
  · fin_cases i
    · cases he
      exact Or.inr (Or.inl ⟨BinaryNormalCharacters8T21.N0.physicalCriterion⟩)
    · cases he
      exact Or.inr (Or.inr ⟨2,BinaryNormalTransport8T21.source_eq,
        BinaryNormalTransport8T21.axis_eq⟩)
    · exact False.elim ((by decide +kernel : ¬(2 : Fin 12)∈BinaryPairInstalled8T21.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(3 : Fin 12)∈BinaryPairInstalled8T21.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(4 : Fin 12)∈BinaryPairInstalled8T21.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(5 : Fin 12)∈BinaryPairInstalled8T21.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(6 : Fin 12)∈BinaryPairInstalled8T21.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(7 : Fin 12)∈BinaryPairInstalled8T21.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(8 : Fin 12)∈BinaryPairInstalled8T21.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(9 : Fin 12)∈BinaryPairInstalled8T21.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(10 : Fin 12)∈BinaryPairInstalled8T21.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(11 : Fin 12)∈BinaryPairInstalled8T21.residualIndices) hi)
end SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T21
