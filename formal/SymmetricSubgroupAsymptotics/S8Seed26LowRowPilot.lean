import SymmetricSubgroupAsymptotics.S8Seed26NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop16CatalogueBinding
import Mathlib.Tactic.FinCases

/-! One actual low-row pilot above original8T26. Bidirectional ordinary
words prove its selected-normalizer invariance and an actual canonical
point binding. No numerical order is a theorem premise. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed26LowRowPilot
open S8Seed26LeftCosets

def lowGenerators : Fin 4 → Ambient :=
  Matrix.vecCons (representatives (S8Seed26NormalizerRoots.roots 16))
    BinaryMenuCayley8T26.generators

def lowRow : Subgroup Ambient := Subgroup.closure (Set.range lowGenerators)

theorem low_eq_adjoin : lowRow =
    H ⊔ Subgroup.closure {representatives (S8Seed26NormalizerRoots.roots 16)} := by
  simp only [lowRow, lowGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

theorem seed_le_low : H ≤ lowRow := by
  rw [low_eq_adjoin]
  exact le_sup_left

def normalizerCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed26NormalizerRoots.normalizer)
    lowGenerators lowGenerators where
  forward := {
    words := ![(.mul (.mul (.generator 2) (.generator 0)) (.mul (.generator 3) (.generator 0))), (.mul (.inv (.generator 0)) (.mul (.inv (.generator 0)) (.generator 3))), (.mul (.generator 1) (.mul (.generator 2) (.inv (.generator 1)))), (.mul (.mul (.generator 0) (.generator 0)) (.mul (.inv (.generator 1)) (.generator 2)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 1) (.inv (.generator 0))) (.mul (.inv (.generator 1)) (.generator 2))), (.mul (.generator 1) (.generator 2)), (.mul (.generator 3) (.mul (.generator 2) (.generator 3))), (.mul (.generator 1) (.mul (.generator 1) (.generator 3)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem normalizes_low : MulAut.conj S8Seed26NormalizerRoots.normalizer • lowRow = lowRow := by
  change lowRow.map (MulAut.conj S8Seed26NormalizerRoots.normalizer).toMonoidHom = lowRow
  exact normalizerCertificate.map_closure_eq

def conjugator : Ambient where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def canonicalCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    lowGenerators PrimitiveAffineEightTop16CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.mul (.generator 0) (.mul (.generator 2) (.generator 3))) (.mul (.generator 1) (.mul (.generator 2) (.generator 0)))), (.mul (.generator 3) (.mul (.generator 1) (.generator 2))), (.generator 0), (.mul (.mul (.generator 0) (.generator 3)) (.mul (.generator 2) (.generator 0)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 2), (.mul (.generator 1) (.mul (.generator 2) (.generator 3))), (.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 1) (.generator 1))), (.mul (.mul (.generator 0) (.generator 2)) (.mul (.inv (.generator 1)) (.mul (.generator 2) (.generator 3))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem canonical_conjugated : MulAut.conj conjugator • lowRow = PrimitiveAffineEightTop16CatalogueBinding.catalogueAction := by
  change lowRow.map (MulAut.conj conjugator).toMonoidHom =
    Subgroup.closure (Set.range PrimitiveAffineEightTop16CatalogueBinding.catalogueGenerators)
  exact canonicalCertificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed26LowRowPilot
end
