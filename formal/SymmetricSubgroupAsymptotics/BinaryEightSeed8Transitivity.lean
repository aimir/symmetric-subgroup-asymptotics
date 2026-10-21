import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T8
import SymmetricSubgroupAsymptotics.FinitePointWordCertificate
import SymmetricSubgroupAsymptotics.BinarySylowCoverage
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! The first literal8T8 generator is the displayed8-cycle. Its first
eight powers give a small original-point transitivity certificate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightSeed8Transitivity

private def g : FiniteGeneratorWord (Fin 2) := .generator 0

def certificate : FinitePointWordCertificate BinaryMenuCayley8T8.generators where
  basePoint := 0
  words := ![.one, g, .mul g g, .mul g (.mul g g),
    .mul (.mul g g) (.mul g g), .mul g (.mul (.mul g g) (.mul g g)),
    .mul (.mul g g) (.mul (.mul g g) (.mul g g)),
    .mul g (.mul (.mul g g) (.mul (.mul g g) (.mul g g)))]
  reaches := by
    intro x
    fin_cases x <;> decide +kernel

theorem transitive : PermutationSubgroupTransitive
    (Subgroup.closure (Set.range BinaryMenuCayley8T8.generators)) := by
  intro x y
  obtain ⟨g, hg⟩ := certificate.pretransitive.exists_smul_eq x y
  exact ⟨g.val, g.property, hg⟩

end SymmetricSubgroupAsymptotics.BinaryEightSeed8Transitivity
end
