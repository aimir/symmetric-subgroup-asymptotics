import SymmetricSubgroupAsymptotics.S8Seed4LowModels
import SymmetricSubgroupAsymptotics.FiniteSubgroupJoinWords

/-! One actual low-row equality certified by ordinary words in both
directions. No cardinality or catalogue correspondence is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed4LowJoin2_4
open S8Seed4LeftCosets S8Seed4LowModels

def sourceGenerators (k : Fin 6) : Ambient :=
  Fin.addCases (m := 3) (n := 3) (generators 2) (generators 4) k

def certificate : FiniteGeneratorEquivWordCertificate (MulEquiv.refl Ambient)
    sourceGenerators (generators 1) where
  forward := {
    words := ![(.mul (.mul (.generator 1) (.mul (.generator 0) (.generator 1))) (.mul (.generator 2) (.mul (.inv (.generator 0)) (.inv (.generator 1))))), (.generator 1), (.generator 2), (.mul (.mul (.generator 0) (.generator 2)) (.mul (.generator 0) (.mul (.generator 1) (.generator 0)))), (.generator 1), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 3) (.generator 2))), (.generator 1), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem join_eq : rows 2 ⊔ rows 4 = rows 1 :=
  FiniteSubgroupAdjunctionCoverage.sup_eq_of_words (generators 2) (generators 4)
    (generators 1) certificate

end SymmetricSubgroupAsymptotics.S8Seed4LowJoin2_4
end
