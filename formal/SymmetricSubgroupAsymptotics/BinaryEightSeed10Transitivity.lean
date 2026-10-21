import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T10
import SymmetricSubgroupAsymptotics.FinitePointWordCertificate
import SymmetricSubgroupAsymptotics.BinarySylowCoverage
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Eight explicit original-point words for literal8T10. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightSeed10Transitivity

private def a : FiniteGeneratorWord (Fin 2) := .generator 0
private def h : FiniteGeneratorWord (Fin 2) := .generator 1
private def h2 : FiniteGeneratorWord (Fin 2) := .mul h h
private def h3 : FiniteGeneratorWord (Fin 2) := .mul h h2

def certificate : FinitePointWordCertificate BinaryMenuCayley8T10.generators where
  basePoint := 0
  words := ![.one, h, h2, .mul h3 a, a, .mul h a, .mul h2 a, h3]
  reaches := by
    intro x
    fin_cases x <;> decide +kernel

theorem transitive : PermutationSubgroupTransitive
    (Subgroup.closure (Set.range BinaryMenuCayley8T10.generators)) := by
  intro x y
  obtain ⟨g, hg⟩ := certificate.pretransitive.exists_smul_eq x y
  exact ⟨g.val, g.property, hg⟩

end SymmetricSubgroupAsymptotics.BinaryEightSeed10Transitivity
end
