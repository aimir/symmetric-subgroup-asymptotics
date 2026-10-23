import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticSpace
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTorusParameters

/-! Exact fixed-field linear parameters on the SAME defining-fixed
space: two untouched coordinate strings and one quadratic-extension
coordinate. The actual quadratic form is dot(x,y)+Norm(a), retaining
the anisotropic final plane in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDLinearParameters
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDFixedVectorCardinality CFSGTwistedDFixedVectorParametrization
open CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticForm

def linearParameters (n : ℕ) (q : CFSG.PrimePower) :
    fixedSpace n q ≃ₗ[fixedField q]
      ((Fin (n + 1) → fixedField q) × ((Fin (n + 1) → fixedField q) × q.Extension 2)) where
  toFun v := coordinateEncoding n q (fixedCarrierEquiv n q v)
  invFun x := ⟨fromParameters n q x, fromParameters_fixed n q x⟩
  left_inv v := by
    apply Subtype.ext
    exact congrArg Subtype.val ((parameterEquiv n q).left_inv (fixedCarrierEquiv n q v))
  right_inv x := encoding_parameterVector n q x
  map_add' v w := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      rfl
    · apply Prod.ext
      · funext i
        apply Subtype.ext
        rfl
      · rfl
  map_smul' a v := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      rfl
    · apply Prod.ext
      · funext i
        apply Subtype.ext
        rfl
      · rfl

theorem linearParameters_symm_val (n : ℕ) (q : CFSG.PrimePower) (x : Parameters n q) :
    ((linearParameters n q).symm x).val = fromParameters n q x := rfl

theorem norm_coe (q : CFSG.PrimePower) (a : q.Extension 2) :
    ((Algebra.norm (fixedField q) a : fixedField q) : q.Extension 2) =
      a * definingFieldAutomorphism q 2 a := by
  have he := FiniteField.algebraMap_norm_eq_pow
    (K := fixedField q) (K' := q.Extension 2) (x := a)
  rw [CFSGTwistedANaturalMatrices.extension_two_card, fixedField_card,
    CFSGTwistedA2UnipotentArrays.normExponent] at he
  simpa only [pow_succ, definingFieldAutomorphism_apply, mul_comm] using he

theorem quadratic_parameters (n : ℕ) (q : CFSG.PrimePower) (x : Parameters n q) :
    fixedQuadraticForm n q ((linearParameters n q).symm x) =
      (∑ i : Fin (n + 1), x.1 i * x.2.1 i) + Algebra.norm (fixedField q) x.2.2 := by
  apply Subtype.ext
  rw [fixedQuadraticForm_apply, linearParameters_symm_val, splitQuadraticForm_apply]
  change (∑ i : Fin (n + 2), fromParameters n q x (Sum.inl i) *
    fromParameters n q x (Sum.inr i)) =
      (fixedField q).subtype ((∑ i : Fin (n + 1), x.1 i * x.2.1 i) +
        Algebra.norm (fixedField q) x.2.2)
  rw [map_add, map_sum, Fin.sum_univ_castSucc]
  simp only [fromParameters, Fin.lastCases_castSucc, Fin.lastCases_last,
    map_mul, Subfield.subtype_apply, norm_coe]

end SymmetricSubgroupAsymptotics.CFSGTwistedDLinearParameters
