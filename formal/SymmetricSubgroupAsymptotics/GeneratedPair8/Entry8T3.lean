import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry8
import SymmetricSubgroupAsymptotics.GeneratedPair8.Installed8T3

/-! All original normal states of 8T3 enter their checked finite branch.
Character counting and the whole-family weighted sum remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T3
local instance : Group BinaryNormal8T3.Source := BinaryMenuCayley8T3.group
abbrev Original := BinaryPairInstalled8T3.Original

/-- No semantic acceptance or normal-enumeration premise is required. -/
theorem finiteEntryCoverage (N : Subgroup Original) [N.Normal] : BinaryFiniteEntry8 Original N := by
  rcases BinaryPairInstalled8T3.normal_coverage N with ⟨j,rfl⟩|⟨i,hi,he⟩
  · exact Or.inl ⟨{
      pairCount := 4
      frame := BinaryPairInstalled8T3.frame
      generatorCount := 3
      generators := BinaryPairInstalled8T3.generators
      generators_full := BinaryPairInstalled8T3.generators_full
      localCertificate := BinaryPairInstalled8T3.physicalCertificates j
      physical_width := BinaryPairInstalled8T3.physical_width j }⟩
  · fin_cases i
    · exact False.elim ((by decide +kernel : ¬(0 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(1 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(2 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(3 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(4 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(5 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(6 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(7 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(8 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(9 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(10 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(11 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(12 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(13 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(14 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(15 : Fin 16)∈BinaryPairInstalled8T3.residualIndices) hi)
end SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T3
