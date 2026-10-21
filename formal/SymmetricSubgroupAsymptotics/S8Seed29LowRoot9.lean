import SymmetricSubgroupAsymptotics.S8Seed29LowModels

/-! One exact repeated-low-root binding above original8T29. Ordinary
words prove both generator inclusions in the actual permutation groups. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed29LowRoot9
open S8Seed29LeftCosets S8Seed29LowModels

def certificate : FiniteGeneratorEqualityCertificate (rootGenerators 9)
    (generators 2) where
  forward := {
    words := ![(.mul (.generator 0) (.generator 0)), (.generator 1), (.generator 2), (.generator 3), (.generator 4), (.generator 5)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.inv (.generator 0)) (.mul (.inv (.generator 0)) (.inv (.generator 0)))), (.generator 1), (.generator 2), (.generator 3), (.generator 4), (.generator 5)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : H ⊔ Subgroup.closure
    {representatives (S8Seed29NormalizerRoots.roots 9)} = rows 2 := by
  rw [← root_closure]
  exact certificate.closure_eq

end SymmetricSubgroupAsymptotics.S8Seed29LowRoot9
end
