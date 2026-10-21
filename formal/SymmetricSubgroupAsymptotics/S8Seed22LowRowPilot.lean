import SymmetricSubgroupAsymptotics.S8Seed22NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop12CatalogueBinding
import Mathlib.Tactic.FinCases

/-! One actual low-row pilot above original8T22. Bidirectional ordinary
words prove its selected-normalizer invariance and an actual canonical
point binding. No numerical order is a theorem premise. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed22LowRowPilot
open S8Seed22LeftCosets

def lowGenerators : Fin 6 → Ambient :=
  Matrix.vecCons (representatives (S8Seed22NormalizerRoots.roots 45))
    BinaryMenuCayley8T22.generators

def lowRow : Subgroup Ambient := Subgroup.closure (Set.range lowGenerators)

theorem low_eq_adjoin : lowRow =
    H ⊔ Subgroup.closure {representatives (S8Seed22NormalizerRoots.roots 45)} := by
  simp only [lowRow, lowGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

theorem seed_le_low : H ≤ lowRow := by
  rw [low_eq_adjoin]
  exact le_sup_left

def normalizerCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed22NormalizerRoots.normalizer)
    lowGenerators lowGenerators where
  forward := {
    words := ![(.mul (.inv (.generator 0)) (.generator 3)), (.generator 1), (.mul (.generator 2) (.generator 3)), (.generator 3), (.mul (.generator 0) (.mul (.generator 5) (.inv (.generator 0)))), (.mul (.generator 1) (.generator 5))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 3) (.inv (.generator 0))), (.generator 1), (.mul (.generator 2) (.generator 3)), (.generator 3), (.mul (.generator 4) (.generator 5)), (.mul (.generator 1) (.generator 5))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem normalizes_low : MulAut.conj S8Seed22NormalizerRoots.normalizer • lowRow = lowRow := by
  change lowRow.map (MulAut.conj S8Seed22NormalizerRoots.normalizer).toMonoidHom = lowRow
  exact normalizerCertificate.map_closure_eq

def conjugator : Ambient where
  toFun := ![0, 1, 4, 2, 3, 6, 7, 5]
  invFun := ![0, 1, 3, 4, 2, 7, 5, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def canonicalCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    lowGenerators PrimitiveAffineEightTop12CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.mul (.generator 0) (.generator 4)) (.mul (.generator 3) (.generator 4))), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.generator 2), (.mul (.generator 0) (.generator 2)), (.generator 4), (.mul (.mul (.generator 0) (.generator 3)) (.mul (.generator 2) (.mul (.generator 4) (.inv (.generator 3)))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 2) (.generator 3)), (.mul (.generator 1) (.generator 3)), (.generator 2), (.mul (.generator 0) (.mul (.generator 5) (.generator 2))), (.generator 4)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem canonical_conjugated : MulAut.conj conjugator • lowRow = PrimitiveAffineEightTop12CatalogueBinding.catalogueAction := by
  change lowRow.map (MulAut.conj conjugator).toMonoidHom =
    Subgroup.closure (Set.range PrimitiveAffineEightTop12CatalogueBinding.catalogueGenerators)
  exact canonicalCertificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed22LowRowPilot
end
