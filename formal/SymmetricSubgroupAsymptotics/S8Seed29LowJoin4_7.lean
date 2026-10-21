import SymmetricSubgroupAsymptotics.S8Seed29LowModels

/-! One exact low join above original8T29:models4 and7 give model3.
Both inclusions follow from ordinary words in actual permutations. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed29LowJoin4_7
open S8Seed29LeftCosets

def sourceGenerators (k : Fin 12) : Ambient :=
  Fin.addCases (m := 6) (n := 6) (S8Seed29LowModels.generators 4)
    (S8Seed29LowModels.generators 7) k

def certificate : FiniteGeneratorEquivWordCertificate (MulEquiv.refl Ambient)
    sourceGenerators (S8Seed29LowModels.generators 3) where
  forward := {
    words := ![(.mul (.mul (.generator 5) (.generator 0)) (.mul (.generator 3) (.inv (.generator 0)))), (.generator 1), (.generator 2), (.generator 3), (.generator 4), (.generator 5), (.mul (.mul (.generator 0) (.generator 2)) (.mul (.generator 3) (.mul (.generator 0) (.generator 1)))), (.mul (.generator 0) (.mul (.generator 1) (.inv (.generator 0)))), (.generator 2), (.mul (.generator 2) (.mul (.generator 3) (.generator 5))), (.generator 4), (.generator 5)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 6) (.generator 4))), (.generator 1), (.generator 2), (.generator 3), (.generator 4), (.generator 5)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : S8Seed29LowModels.rows 4 ⊔ S8Seed29LowModels.rows 7 =
    S8Seed29LowModels.rows 3 :=
  FiniteSubgroupAdjunctionCoverage.sup_eq_of_words _ _ _ certificate

end SymmetricSubgroupAsymptotics.S8Seed29LowJoin4_7
end
