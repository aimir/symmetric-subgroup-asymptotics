import SymmetricSubgroupAsymptotics.S8Sylow128DoubleCosets
import SymmetricSubgroupAsymptotics.S8Sylow128SelectedRows
import SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionWords

/-! One selected ordinary-word adjunction witness, double-coset root6.
Both actual generator inclusions are checked in the original permutation
group. No order or producer acceptance is used as a theorem premise. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Sylow128AdjunctionRoot6
open S8Sylow128LeftCosets

def conjugator : Ambient where
  toFun := ![0, 3, 1, 4, 2, 5, 7, 6]
  invFun := ![0, 2, 4, 1, 3, 5, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sourceGenerators : Fin 4 → Ambient :=
  Matrix.vecCons (representatives (S8Sylow128DoubleCosets.roots 6))
    BinaryMenuCayley8T35.generators

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    sourceGenerators PrimitiveAffineEightTop10CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.inv (.generator 0)) (.mul (.generator 1) (.generator 0))), (.mul (.mul (.generator 2) (.mul (.generator 0) (.generator 1))) (.mul (.mul (.generator 0) (.generator 0)) (.mul (.generator 1) (.generator 2)))), (.mul (.mul (.generator 1) (.generator 0)) (.mul (.generator 0) (.generator 1))), (.mul (.mul (.mul (.generator 0) (.generator 0)) (.mul (.generator 2) (.generator 0))) (.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 0) (.mul (.generator 0) (.generator 1)))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 2) (.inv (.generator 3))) (.mul (.generator 1) (.generator 3))), (.mul (.mul (.generator 0) (.generator 3)) (.mul (.generator 1) (.mul (.inv (.generator 3)) (.generator 0)))), (.mul (.mul (.mul (.generator 1) (.generator 2)) (.mul (.generator 3) (.generator 1))) (.mul (.mul (.generator 3) (.generator 1)) (.mul (.generator 3) (.generator 1))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem step : ∃ j : Fin 5, ∃ c : Ambient,
    MulAut.conj c • (H ⊔ Subgroup.closure
      {representatives (S8Sylow128DoubleCosets.roots 6)}) = S8Sylow128SelectedRows.rows j := by
  exact ⟨3, conjugator,
    FiniteSubgroupAdjunctionCoverage.adjoin_eq_of_words _ _ _ _ certificate⟩

end SymmetricSubgroupAsymptotics.S8Sylow128AdjunctionRoot6
end
