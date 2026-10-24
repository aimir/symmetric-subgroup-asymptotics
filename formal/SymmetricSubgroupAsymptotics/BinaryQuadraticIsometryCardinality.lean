import SymmetricSubgroupAsymptotics.BinaryQuadraticIsometryLeadingCardinality
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-! Basis changes remove the leading-coefficient hypothesis from the
literal characteristic-two binary quadratic isometry bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.BinaryQuadraticIsometryCardinality

open BinaryQuadraticIsometryLeadingCardinality
variable {K : Type*} [Field K]

private theorem cancel_mulVec (T : GeneralLinear (K := K)) (v : Fin 2 → K) :
    T.val *ᵥ ((T⁻¹).val *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mulVec]

/-- An actual change of basis injects the two literal isometry groups. -/
theorem card_le_of_change_of_basis [Finite K]
    (a b c a' b' c' : K) (T : GeneralLinear (K := K))
    (hT : ∀ v : Fin 2 → K,
      vectorEval a b c (T.val *ᵥ v) = vectorEval a' b' c' v) :
    Nat.card (isometries a b c) ≤ Nat.card (isometries a' b' c') := by
  let f : isometries a b c → isometries a' b' c' := fun g =>
    ⟨T⁻¹ * g.val * T, by
      intro v
      have hc : T.val *ᵥ ((T⁻¹ * g.val * T).val *ᵥ v) =
          g.val.val *ᵥ (T.val *ᵥ v) := by
        simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
        exact cancel_mulVec T _
      calc
        vectorEval a' b' c' ((T⁻¹ * g.val * T).val *ᵥ v) =
            vectorEval a b c (T.val *ᵥ ((T⁻¹ * g.val * T).val *ᵥ v)) := (hT _).symm
        _ = vectorEval a b c (T.val *ᵥ v) := by rw [hc, g.property]
        _ = vectorEval a' b' c' v := hT v⟩
  apply Nat.card_le_card_of_injective f
  intro g h he
  apply Subtype.ext
  have hv : T⁻¹ * g.val * T = T⁻¹ * h.val * T := congrArg Subtype.val he
  exact mul_left_cancel (mul_right_cancel hv)

private def swapBasis : GeneralLinear (K := K) where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    norm_num [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact Matrix.one_fin_two.symm
  inv_val := by
    norm_num [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact Matrix.one_fin_two.symm

private def shearBasis : GeneralLinear (K := K) where
  val := !![1, 0; 1, 1]
  inv := !![1, 0; -1, 1]
  val_inv := by
    norm_num [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact Matrix.one_fin_two.symm
  inv_val := by
    norm_num [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact Matrix.one_fin_two.symm

/-- Every nondegenerate binary quadratic form in characteristic two has
at most four times the field cardinality many literal linear isometries. -/
theorem card_le_four_mul_card [Finite K] [CharP K 2]
    (a b c : K) (hb : b ≠ 0) :
    Nat.card (isometries a b c) ≤ 4 * Nat.card K := by
  by_cases ha : a ≠ 0
  · exact card_le_four_mul_card_of_leading_ne_zero a b c ha hb
  by_cases hc : c ≠ 0
  · apply (card_le_of_change_of_basis a b c c b a swapBasis ?_).trans
      (card_le_four_mul_card_of_leading_ne_zero c b a hc hb)
    intro v
    simp [vectorEval, BinaryQuadraticLevelCardinality.eval, swapBasis,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · have ha0 : a = 0 := not_ne_iff.mp ha
    have hc0 : c = 0 := not_ne_iff.mp hc
    subst a
    subst c
    apply (card_le_of_change_of_basis 0 b 0 b b 0 shearBasis ?_).trans
      (card_le_four_mul_card_of_leading_ne_zero b b 0 hb hb)
    intro v
    simp [vectorEval, BinaryQuadraticLevelCardinality.eval, shearBasis,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

end SymmetricSubgroupAsymptotics.BinaryQuadraticIsometryCardinality
