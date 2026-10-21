import SymmetricSubgroupAsymptotics.S8Seed18LowModels

/-! One ordinary-word join certificate for the actual low-row diamond. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed18LowJoin2_3
open S8Seed18LeftCosets

def sourceGenerators (k : Fin 12) : Ambient :=
  Fin.addCases (m := 6) (n := 6) (S8Seed18LowModels.generators 2)
    (S8Seed18LowModels.generators 3) k

def certificate : FiniteGeneratorEquivWordCertificate (MulEquiv.refl Ambient)
    sourceGenerators (S8Seed18LowModels.generators 1) where
  forward := {
    words := ![(.mul (.mul (.generator 4) (.inv (.generator 0))) (.mul (.generator 3) (.generator 0))), (.generator 1), (.generator 2), (.generator 3), (.generator 4), (.generator 5), (.mul (.mul (.generator 0) (.generator 4)) (.mul (.generator 3) (.generator 0))), (.generator 1), (.generator 2), (.generator 3), (.generator 4), (.generator 5)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 0) (.inv (.generator 6))), (.generator 1), (.generator 2), (.generator 3), (.generator 4), (.generator 5)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : S8Seed18LowModels.rows 2 ⊔ S8Seed18LowModels.rows 3 =
    S8Seed18LowModels.rows 1 :=
  FiniteSubgroupAdjunctionCoverage.sup_eq_of_words _ _ _ certificate

end SymmetricSubgroupAsymptotics.S8Seed18LowJoin2_3
end
