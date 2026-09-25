import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry8
import SymmetricSubgroupAsymptotics.GeneratedPair8.Installed8T9

/-! All original normal states of 8T9 enter their checked finite branch.
Character counting and the whole-family weighted sum remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T9
local instance : Group BinaryNormal8T9.Source := BinaryMenuCayley8T9.group
abbrev Original := BinaryPairInstalled8T9.Original

/-- No semantic acceptance or normal-enumeration premise is required. -/
theorem finiteEntryCoverage (N : Subgroup Original) [N.Normal] : BinaryFiniteEntry8 Original N := by
  rcases BinaryPairInstalled8T9.normal_coverage N with ⟨j,rfl⟩|⟨i,hi,he⟩
  · exact Or.inl ⟨{
      pairCount := 4
      frame := BinaryPairInstalled8T9.frame
      generatorCount := 4
      generators := BinaryPairInstalled8T9.generators
      generators_full := BinaryPairInstalled8T9.generators_full
      localCertificate := BinaryPairInstalled8T9.physicalCertificates j
      physical_width := BinaryPairInstalled8T9.physical_width j }⟩
  · fin_cases i
    · exact False.elim ((by decide +kernel : ¬(0 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(1 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(2 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(3 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(4 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(5 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(6 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(7 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(8 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(9 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(10 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(11 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(12 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(13 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(14 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(15 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(16 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(17 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
    · exact False.elim ((by decide +kernel : ¬(18 : Fin 19)∈BinaryPairInstalled8T9.residualIndices) hi)
end SymmetricSubgroupAsymptotics.BinaryFiniteEntry8T9
