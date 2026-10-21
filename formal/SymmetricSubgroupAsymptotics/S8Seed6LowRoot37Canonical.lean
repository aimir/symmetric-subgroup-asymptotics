import SymmetricSubgroupAsymptotics.S8Seed6NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop22CatalogueBinding
import Mathlib.Tactic.FinCases

/-! One actual low-root point binding above original8T6. Bidirectional
ordinary words retain the literal conjugator and canonical Top22 action.
No low-row normalizer fixation or catalogue completeness is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed6LowRoot37Canonical
open S8Seed6LeftCosets

def lowGenerators : Fin 3 → Ambient :=
  Matrix.vecCons (representatives (S8Seed6NormalizerRoots.roots 37))
    BinaryMenuCayley8T6.generators

def lowRow : Subgroup Ambient := Subgroup.closure (Set.range lowGenerators)

theorem low_eq_adjoin : lowRow =
    H ⊔ Subgroup.closure {representatives (S8Seed6NormalizerRoots.roots 37)} := by
  simp only [lowRow, lowGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

theorem seed_le_low : H ≤ lowRow := by
  rw [low_eq_adjoin]
  exact le_sup_left

def conjugator : Ambient where
  toFun := ![0, 1, 2, 5, 3, 6, 7, 4]
  invFun := ![0, 1, 2, 4, 7, 3, 5, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def canonicalCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    lowGenerators PrimitiveAffineEightTop22CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.mul (.generator 0) (.mul (.generator 2) (.generator 1))) (.mul (.generator 0) (.mul (.generator 1) (.generator 2)))), (.mul (.mul (.generator 1) (.generator 1)) (.mul (.generator 2) (.mul (.generator 0) (.inv (.generator 1))))), (.mul (.mul (.generator 0) (.generator 2)) (.mul (.generator 1) (.mul (.generator 1) (.inv (.generator 0)))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 2) (.generator 1)) (.mul (.generator 0) (.mul (.generator 1) (.generator 0)))), (.mul (.mul (.generator 1) (.mul (.generator 0) (.generator 1))) (.mul (.generator 1) (.mul (.generator 1) (.generator 1)))), (.mul (.generator 2) (.mul (.generator 1) (.generator 1)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem canonical_conjugated : MulAut.conj conjugator • lowRow =
    PrimitiveAffineEightTop22CatalogueBinding.catalogueAction := by
  change lowRow.map (MulAut.conj conjugator).toMonoidHom =
    Subgroup.closure (Set.range PrimitiveAffineEightTop22CatalogueBinding.catalogueGenerators)
  exact canonicalCertificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed6LowRoot37Canonical
end
