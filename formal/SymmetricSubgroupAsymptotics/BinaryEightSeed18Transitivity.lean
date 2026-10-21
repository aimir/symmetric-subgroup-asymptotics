import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T18
import SymmetricSubgroupAsymptotics.FinitePointWordCertificate
import SymmetricSubgroupAsymptotics.BinarySylowCoverage
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Eight short orbit words in the original five-generator alphabet certify
transitivity of literal8T18 on its actual points. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightSeed18Transitivity
private def g : FiniteGeneratorWord (Fin 5) := .generator 0
private def h : FiniteGeneratorWord (Fin 5) := .generator 1
private def k : FiniteGeneratorWord (Fin 5) := .generator 2

def certificate : FinitePointWordCertificate BinaryMenuCayley8T18.generators where
  basePoint := 0
  words := ![.one, .mul g h, h, .mul g k, k, .mul g (.mul k h), .mul k h, g]
  reaches := by
    intro x
    fin_cases x <;> decide +kernel

theorem transitive : PermutationSubgroupTransitive
    (Subgroup.closure (Set.range BinaryMenuCayley8T18.generators)) := by
  intro x y
  obtain ⟨g, hg⟩ := certificate.pretransitive.exists_smul_eq x y
  exact ⟨g.val, g.property, hg⟩

end SymmetricSubgroupAsymptotics.BinaryEightSeed18Transitivity
end
