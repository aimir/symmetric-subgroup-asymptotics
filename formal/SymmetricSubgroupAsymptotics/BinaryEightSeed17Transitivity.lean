import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T17
import SymmetricSubgroupAsymptotics.FinitePointWordCertificate
import SymmetricSubgroupAsymptotics.BinarySylowCoverage
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Eight original point-orbit words establish transitivity for literal8T17.
No group-order or abstract action classification is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightSeed17Transitivity

private def g : FiniteGeneratorWord (Fin 2) := .generator 0
private def h : FiniteGeneratorWord (Fin 2) := .generator 1

def certificate : FinitePointWordCertificate BinaryMenuCayley8T17.generators where
  basePoint := 0
  words := ![.one, g, .mul g g, .mul h (.mul g (.mul g g)),
    h, .mul h g, .mul h (.mul g g), .mul g (.mul g g)]
  reaches := by
    intro x
    fin_cases x <;> decide +kernel

theorem transitive : PermutationSubgroupTransitive
    (Subgroup.closure (Set.range BinaryMenuCayley8T17.generators)) := by
  intro x y
  obtain ⟨g, hg⟩ := certificate.pretransitive.exists_smul_eq x y
  exact ⟨g.val, g.property, hg⟩

end SymmetricSubgroupAsymptotics.BinaryEightSeed17Transitivity
end
