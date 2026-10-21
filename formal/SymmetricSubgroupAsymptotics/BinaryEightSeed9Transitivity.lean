import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T9
import SymmetricSubgroupAsymptotics.FinitePointWordCertificate
import SymmetricSubgroupAsymptotics.BinarySylowCoverage
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Eight explicit original-point words for literal8T9. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightSeed9Transitivity

private def a : FiniteGeneratorWord (Fin 4) := .generator 0
private def b : FiniteGeneratorWord (Fin 4) := .generator 1
private def c : FiniteGeneratorWord (Fin 4) := .generator 2

def certificate : FinitePointWordCertificate BinaryMenuCayley8T9.generators where
  basePoint := 0
  words := ![.one, .mul a b, b, .mul a c, c, .mul a (.mul b c), .mul b c, a]
  reaches := by
    intro x
    fin_cases x <;> decide +kernel

theorem transitive : PermutationSubgroupTransitive
    (Subgroup.closure (Set.range BinaryMenuCayley8T9.generators)) := by
  intro x y
  obtain ⟨g, hg⟩ := certificate.pretransitive.exists_smul_eq x y
  exact ⟨g.val, g.property, hg⟩

end SymmetricSubgroupAsymptotics.BinaryEightSeed9Transitivity
end
