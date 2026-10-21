import SymmetricSubgroupAsymptotics.S8Sylow128LiteralModels
import SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionWords
import Mathlib.Tactic.FinCases

/-! One exact literal seed-adjunction equality. Both actual generator
inclusions are certified by ordinary words, with identity conjugator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot10
open S8Sylow128LeftCosets

def sourceGenerators : Fin 4 → Ambient :=
  Matrix.vecCons (representatives (S8Sylow128DoubleCosets.roots 10))
    BinaryMenuCayley8T35.generators

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj (1 : Ambient))
    sourceGenerators (S8Sylow128LiteralModels.generators 3) where
  forward := {
    words := ![(.mul (.mul (.mul (.generator 0) (.mul (.generator 1) (.generator 2))) (.mul (.mul (.inv (.generator 3)) (.generator 1)) (.mul (.inv (.generator 3)) (.generator 0)))) (.mul (.mul (.mul (.generator 3) (.generator 1)) (.mul (.generator 3) (.generator 1))) (.mul (.mul (.generator 3) (.generator 3)) (.mul (.generator 0) (.generator 3))))), (.generator 1), (.generator 2), (.generator 3)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 0) (.mul (.generator 2) (.generator 0))) (.mul (.generator 2) (.mul (.inv (.generator 0)) (.generator 2)))), (.generator 1), (.generator 2), (.generator 3)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : H ⊔ Subgroup.closure
    {representatives (S8Sylow128DoubleCosets.roots 10)} =
      S8Sylow128LiteralModels.rows 3 := by
  simpa only [map_one, one_smul] using
    FiniteSubgroupAdjunctionCoverage.adjoin_eq_of_words _ _ _ 1 certificate

end SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot10
end
