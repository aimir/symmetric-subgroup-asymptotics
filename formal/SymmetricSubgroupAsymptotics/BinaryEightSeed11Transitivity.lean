import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T11
import SymmetricSubgroupAsymptotics.FinitePointWordCertificate
import SymmetricSubgroupAsymptotics.BinarySylowCoverage
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Eight explicit original-point words for literal8T11. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightSeed11Transitivity

private def h : FiniteGeneratorWord (Fin 3) := .generator 1
private def k : FiniteGeneratorWord (Fin 3) := .generator 2
private def h2 : FiniteGeneratorWord (Fin 3) := .mul h h
private def h3 : FiniteGeneratorWord (Fin 3) := .mul h h2

def certificate : FinitePointWordCertificate BinaryMenuCayley8T11.generators where
  basePoint := 0
  words := ![.one, .mul h3 k, h, k, h2, .mul h k, h3, .mul h2 k]
  reaches := by
    intro x
    fin_cases x <;> decide +kernel

theorem transitive : PermutationSubgroupTransitive
    (Subgroup.closure (Set.range BinaryMenuCayley8T11.generators)) := by
  intro x y
  obtain ⟨g, hg⟩ := certificate.pretransitive.exists_smul_eq x y
  exact ⟨g.val, g.property, hg⟩

end SymmetricSubgroupAsymptotics.BinaryEightSeed11Transitivity
end
