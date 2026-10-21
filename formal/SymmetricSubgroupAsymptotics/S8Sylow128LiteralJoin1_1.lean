import SymmetricSubgroupAsymptotics.S8Sylow128LiteralModels
import SymmetricSubgroupAsymptotics.FiniteSubgroupJoinWords
import Mathlib.Tactic.FinCases

/-! One exact literal join-table entry, checked by ordinary words in the
actual eight-point permutations. No group-order recognition is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin1_1
open S8Sylow128LeftCosets

def sourceGenerators (k : Fin 8) : Ambient :=
  Fin.addCases (m := 4) (n := 4) (S8Sylow128LiteralModels.generators 1)
    (S8Sylow128LiteralModels.generators 1) k

def certificate : FiniteGeneratorEquivWordCertificate (MulEquiv.refl Ambient)
    sourceGenerators (S8Sylow128LiteralModels.generators 1) where
  forward := {
    words := ![(.generator 0), (.generator 1), (.generator 2), (.generator 3), (.generator 0), (.generator 1), (.generator 2), (.generator 3)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 0), (.generator 1), (.generator 2), (.generator 3)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : S8Sylow128LiteralModels.rows 1 ⊔
    S8Sylow128LiteralModels.rows 1 = S8Sylow128LiteralModels.rows 1 :=
  FiniteSubgroupAdjunctionCoverage.sup_eq_of_words _ _ _ certificate

end SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin1_1
end
