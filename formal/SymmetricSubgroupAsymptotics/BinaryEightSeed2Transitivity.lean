import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T2
import SymmetricSubgroupAsymptotics.FinitePointWordCertificate
import SymmetricSubgroupAsymptotics.BinarySylowCoverage
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Eight explicit original-point words for literal8T2. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightSeed2Transitivity

private def h : FiniteGeneratorWord (Fin 2) := .generator 0
private def b : FiniteGeneratorWord (Fin 2) := .generator 1
private def h2 : FiniteGeneratorWord (Fin 2) := .mul h h
private def h3 : FiniteGeneratorWord (Fin 2) := .mul h h2

def certificate : FinitePointWordCertificate BinaryMenuCayley8T2.generators where
  basePoint := 0
  words := ![.one, h, h2, .mul h3 b, b, .mul h b, .mul h2 b, h3]
  reaches := by
    intro x
    fin_cases x <;> decide +kernel

theorem transitive : PermutationSubgroupTransitive
    (Subgroup.closure (Set.range BinaryMenuCayley8T2.generators)) := by
  intro x y
  obtain ⟨g, hg⟩ := certificate.pretransitive.exists_smul_eq x y
  exact ⟨g.val, g.property, hg⟩

end SymmetricSubgroupAsymptotics.BinaryEightSeed2Transitivity
end
