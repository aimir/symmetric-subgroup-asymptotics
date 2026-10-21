import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T21
import SymmetricSubgroupAsymptotics.FinitePointWordCertificate
import SymmetricSubgroupAsymptotics.BinarySylowCoverage
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Eight explicit original-point orbit words for literal8T21. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightSeed21Transitivity
private def g : FiniteGeneratorWord (Fin 3) := .generator 0
private def h : FiniteGeneratorWord (Fin 3) := .generator 1
private def k : FiniteGeneratorWord (Fin 3) := .generator 2
private def h3 : FiniteGeneratorWord (Fin 3) := .mul h (.mul h h)

def certificate : FinitePointWordCertificate BinaryMenuCayley8T21.generators where
  basePoint := 0
  words := ![.one, .mul k h3, k, h, g, .mul k h, .mul g k, h3]
  reaches := by
    intro x
    fin_cases x <;> decide +kernel

theorem transitive : PermutationSubgroupTransitive
    (Subgroup.closure (Set.range BinaryMenuCayley8T21.generators)) := by
  intro x y
  obtain ⟨g, hg⟩ := certificate.pretransitive.exists_smul_eq x y
  exact ⟨g.val, g.property, hg⟩

end SymmetricSubgroupAsymptotics.BinaryEightSeed21Transitivity
end
