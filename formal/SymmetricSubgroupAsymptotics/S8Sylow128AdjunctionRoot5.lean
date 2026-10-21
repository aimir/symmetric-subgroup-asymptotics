import SymmetricSubgroupAsymptotics.S8Sylow128DoubleCosets
import SymmetricSubgroupAsymptotics.S8Sylow128SelectedRows
import SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionWords

/-! One selected ordinary-word adjunction witness, double-coset root5.
Both actual generator inclusions are checked in the original permutation
group. No order or producer acceptance is used as a theorem premise. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Sylow128AdjunctionRoot5
open S8Sylow128LeftCosets

def conjugator : Ambient where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sourceGenerators : Fin 4 → Ambient :=
  Matrix.vecCons (representatives (S8Sylow128DoubleCosets.roots 5))
    BinaryMenuCayley8T35.generators

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    sourceGenerators PrimitiveAffineEightTop17CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.generator 2) (.mul (.generator 1) (.inv (.generator 2)))), (.generator 0), (.mul (.mul (.generator 1) (.generator 2)) (.mul (.generator 2) (.mul (.generator 1) (.inv (.generator 2))))), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 1), (.mul (.generator 2) (.mul (.generator 0) (.inv (.generator 3)))), (.generator 3)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem step : ∃ j : Fin 5, ∃ c : Ambient,
    MulAut.conj c • (H ⊔ Subgroup.closure
      {representatives (S8Sylow128DoubleCosets.roots 5)}) = S8Sylow128SelectedRows.rows j := by
  exact ⟨1, conjugator,
    FiniteSubgroupAdjunctionCoverage.adjoin_eq_of_words _ _ _ _ certificate⟩

end SymmetricSubgroupAsymptotics.S8Sylow128AdjunctionRoot5
end
