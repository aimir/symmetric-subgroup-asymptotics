import SymmetricSubgroupAsymptotics.S8Seed9NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop6CatalogueBinding
import Mathlib.Tactic.FinCases

/-! One actual low-root point binding above original8T9. Bidirectional
ordinary words retain the literal conjugator and canonical Top6 action.
No low-row normalizer fixation or catalogue completeness is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed9LowRoot8Canonical
open S8Seed9LeftCosets

def lowGenerators : Fin 5 → Ambient :=
  Matrix.vecCons (representatives (S8Seed9NormalizerRoots.roots 8))
    BinaryMenuCayley8T9.generators

def lowRow : Subgroup Ambient := Subgroup.closure (Set.range lowGenerators)

theorem low_eq_adjoin : lowRow =
    H ⊔ Subgroup.closure {representatives (S8Seed9NormalizerRoots.roots 8)} := by
  simp only [lowRow, lowGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

theorem seed_le_low : H ≤ lowRow := by
  rw [low_eq_adjoin]
  exact le_sup_left

def conjugator : Ambient where
  toFun := ![0, 3, 5, 4, 6, 1, 7, 2]
  invFun := ![0, 5, 7, 1, 3, 2, 4, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def canonicalCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    lowGenerators PrimitiveAffineEightTop6CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.generator 4), (.generator 1), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.mul (.generator 1) (.generator 2)), (.mul (.generator 1) (.mul (.generator 4) (.generator 3)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 2) (.generator 3)), (.generator 1), (.mul (.generator 1) (.generator 3)), (.mul (.generator 0) (.mul (.generator 1) (.generator 4))), (.generator 0)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem canonical_conjugated : MulAut.conj conjugator • lowRow =
    PrimitiveAffineEightTop6CatalogueBinding.catalogueAction := by
  change lowRow.map (MulAut.conj conjugator).toMonoidHom =
    Subgroup.closure (Set.range PrimitiveAffineEightTop6CatalogueBinding.catalogueGenerators)
  exact canonicalCertificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed9LowRoot8Canonical
end
