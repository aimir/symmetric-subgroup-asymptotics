import SymmetricSubgroupAsymptotics.S8Seed28NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop9CatalogueBinding
import Mathlib.Tactic.FinCases

/-! One low-row pilot for original8T28. The two selected root adjunctions
are the same literal subgroup, it is fixed by the actual selected
normalizer, and its canonical binding uses an actual point conjugator.
Every assertion follows from ordinary-word equations. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed28LowRowPilot
open S8Seed28LeftCosets

def lowGenerators : Fin 4 → Ambient :=
  Matrix.vecCons (representatives (S8Seed28NormalizerRoots.roots 17))
    BinaryMenuCayley8T28.generators

def lowRow : Subgroup Ambient := Subgroup.closure (Set.range lowGenerators)

theorem low_eq_adjoin : lowRow =
    H ⊔ Subgroup.closure {representatives (S8Seed28NormalizerRoots.roots 17)} := by
  simp only [lowRow, lowGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

theorem seed_le_low : H ≤ lowRow := by
  rw [low_eq_adjoin]
  exact le_sup_left

def otherGenerators : Fin 4 → Ambient :=
  Matrix.vecCons (representatives (S8Seed28NormalizerRoots.roots 21))
    BinaryMenuCayley8T28.generators

def otherEquality : FiniteGeneratorEqualityCertificate otherGenerators lowGenerators where
  forward := {
    words := ![(.mul (.mul (.generator 1) (.generator 0)) (.mul (.inv (.generator 3)) (.mul (.generator 0) (.generator 1)))), (.generator 1), (.generator 2), (.generator 3)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 0) (.generator 0)) (.mul (.generator 1) (.mul (.generator 3) (.generator 3)))), (.generator 1), (.generator 2), (.generator 3)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem other_eq_low : H ⊔ Subgroup.closure
    {representatives (S8Seed28NormalizerRoots.roots 21)} = lowRow := by
  simpa only [otherGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm] using
    otherEquality.closure_eq

def normalizerCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj S8Seed28NormalizerRoots.normalizer)
    lowGenerators lowGenerators where
  forward := {
    words := ![(.mul (.generator 3) (.mul (.generator 0) (.inv (.generator 3)))), (.generator 1), (.generator 2), (.mul (.generator 2) (.mul (.inv (.generator 3)) (.generator 2)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 3) (.mul (.generator 0) (.inv (.generator 3)))), (.generator 1), (.generator 2), (.mul (.generator 2) (.mul (.inv (.generator 3)) (.generator 2)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem normalizes_low : MulAut.conj S8Seed28NormalizerRoots.normalizer • lowRow = lowRow := by
  change lowRow.map (MulAut.conj S8Seed28NormalizerRoots.normalizer).toMonoidHom = lowRow
  exact normalizerCertificate.map_closure_eq

def conjugator : Ambient where
  toFun := ![0, 3, 1, 4, 2, 5, 7, 6]
  invFun := ![0, 2, 4, 1, 3, 5, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def canonicalCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    lowGenerators PrimitiveAffineEightTop9CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.mul (.generator 1) (.generator 3)) (.mul (.generator 0) (.mul (.inv (.generator 1)) (.generator 3)))), (.mul (.mul (.generator 0) (.mul (.generator 3) (.generator 1))) (.mul (.generator 0) (.mul (.generator 3) (.generator 1)))), (.mul (.generator 1) (.mul (.generator 0) (.inv (.generator 1)))), (.mul (.mul (.generator 0) (.generator 3)) (.mul (.generator 0) (.generator 1)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 1) (.generator 2)) (.mul (.generator 1) (.generator 2))), (.mul (.mul (.generator 0) (.mul (.generator 2) (.inv (.generator 3)))) (.mul (.generator 0) (.mul (.generator 3) (.generator 2)))), (.mul (.mul (.generator 0) (.generator 3)) (.mul (.generator 1) (.mul (.inv (.generator 3)) (.generator 0)))), (.mul (.mul (.generator 0) (.inv (.generator 3))) (.mul (.generator 2) (.mul (.generator 1) (.generator 0))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem canonical_conjugated : MulAut.conj conjugator • lowRow = PrimitiveAffineEightTop9CatalogueBinding.catalogueAction := by
  change lowRow.map (MulAut.conj conjugator).toMonoidHom =
    Subgroup.closure (Set.range PrimitiveAffineEightTop9CatalogueBinding.catalogueGenerators)
  exact canonicalCertificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed28LowRowPilot
end
