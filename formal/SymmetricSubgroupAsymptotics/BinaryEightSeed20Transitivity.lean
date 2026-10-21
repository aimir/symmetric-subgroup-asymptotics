import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T20
import SymmetricSubgroupAsymptotics.FinitePointWordCertificate
import SymmetricSubgroupAsymptotics.BinarySylowCoverage
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Eight explicit original-point orbit words for literal8T20. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightSeed20Transitivity
private def g : FiniteGeneratorWord (Fin 2) := .generator 0
private def h : FiniteGeneratorWord (Fin 2) := .generator 1
private def h2 : FiniteGeneratorWord (Fin 2) := .mul h h
private def h3 : FiniteGeneratorWord (Fin 2) := .mul h h2
private def u : FiniteGeneratorWord (Fin 2) := .mul g h

def certificate : FinitePointWordCertificate BinaryMenuCayley8T20.generators where
  basePoint := 0
  words := ![.one, h, h2, .mul h2 u, .mul h3 u, u, .mul h u, h3]
  reaches := by
    intro x
    fin_cases x <;> decide +kernel

theorem transitive : PermutationSubgroupTransitive
    (Subgroup.closure (Set.range BinaryMenuCayley8T20.generators)) := by
  intro x y
  obtain ⟨g, hg⟩ := certificate.pretransitive.exists_smul_eq x y
  exact ⟨g.val, g.property, hg⟩

end SymmetricSubgroupAsymptotics.BinaryEightSeed20Transitivity
end
