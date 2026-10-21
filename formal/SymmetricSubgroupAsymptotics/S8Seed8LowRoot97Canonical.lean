import SymmetricSubgroupAsymptotics.S8Seed8NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop14CatalogueBinding
import Mathlib.Tactic.FinCases

/-! One actual low-root point binding above original8T8. Bidirectional
ordinary words retain the literal conjugator and canonical Top14 action.
No low-row normalizer fixation or catalogue completeness is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed8LowRoot97Canonical
open S8Seed8LeftCosets

def lowGenerators : Fin 3 → Ambient :=
  Matrix.vecCons (representatives (S8Seed8NormalizerRoots.roots 97))
    BinaryMenuCayley8T8.generators

def lowRow : Subgroup Ambient := Subgroup.closure (Set.range lowGenerators)

theorem low_eq_adjoin : lowRow =
    H ⊔ Subgroup.closure {representatives (S8Seed8NormalizerRoots.roots 97)} := by
  simp only [lowRow, lowGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

theorem seed_le_low : H ≤ lowRow := by
  rw [low_eq_adjoin]
  exact le_sup_left

def conjugator : Ambient where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def canonicalCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    lowGenerators PrimitiveAffineEightTop14CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.mul (.inv (.generator 0)) (.generator 1)) (.mul (.generator 0) (.generator 0))), (.generator 0), (.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 0) (.mul (.generator 0) (.inv (.generator 1)))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 1), (.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 0) (.generator 1)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem canonical_conjugated : MulAut.conj conjugator • lowRow =
    PrimitiveAffineEightTop14CatalogueBinding.catalogueAction := by
  change lowRow.map (MulAut.conj conjugator).toMonoidHom =
    Subgroup.closure (Set.range PrimitiveAffineEightTop14CatalogueBinding.catalogueGenerators)
  exact canonicalCertificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed8LowRoot97Canonical
end
