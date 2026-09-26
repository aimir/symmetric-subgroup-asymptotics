import SymmetricSubgroupAsymptotics.BinaryCarrierWordRecursion
import SymmetricSubgroupAsymptotics.BinaryCarrierSourceOrder
import SymmetricSubgroupAsymptotics.BinaryMarkedTrivial

/-! Whole-word induction from the actual marked family recurrence. A common
target constant and the order of the original product control only the
polynomial loss. Every history retains its actual normal axes, quotient
slopes and prefix marks. No row envelope or global recurrence is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryCarrierWord

open FullSubdirectGoursat BinaryMarkedGoursatPeel

attribute [local instance] Fintype.ofFinite

/-- A genuine bound on constants of all original normal quotients.
It carries no assertion about subgroup counts or the desired recurrence. -/
def TargetConstants : List Factor → ℕ → Prop
  | [], _ => True
  | A :: w, C =>
      (∀ N : NormalAxis A.Carrier,
        binaryStructuredEpiConstant (A.Carrier ⧸ N.1) ≤ C) ∧ TargetConstants w C

/-- The full finite sum over actual normal-axis histories, with their
successive quotient tilts. There is no terminal attachment in this definition. -/
def normalHistorySum : (w : List Factor) → AxisWeights w → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _ => 1
  | A :: w, v, x, y, z =>
      ∑ N : NormalAxis A.Carrier, v.1 N * (2 : ℝ)^(cost N x y z) *
        normalHistorySum w v.2 (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z

theorem normalHistorySum_nonneg (w : List Factor) (v : AxisWeights w)
    (hv : WeightsNonnegative w v) (x y z : ℝ) :
    0 ≤ normalHistorySum w v x y z := by
  induction w generalizing x y with
  | nil => exact zero_le_one
  | cons A w ih =>
      apply Finset.sum_nonneg
      intro N _
      exact mul_nonneg (mul_nonneg (hv.1 N) (Real.rpow_nonneg (by norm_num) _))
        (ih v.2 hv.2 _ _)

/-- The suffix is embedded by b |-> (1,b); its order never exceeds the
original word product. No fullness assumption is used for this bound. -/
theorem tail_card_le (A : Factor) (w : List Factor) :
    Nat.card (Product w) ≤ Nat.card (Product (A :: w)) :=
  Nat.card_le_card_of_injective (fun b : Product w => ((1 : A.Carrier),b))
    (fun _ _ h => congrArg (fun p : A.Carrier × Product w => p.2) h)

theorem tail_polynomial_le (A : Factor) (w : List Factor)
    (s C : ℕ) (hcard : Nat.card (Product w) ≤ 2^s)
    (hC : ∀ N : NormalAxis A.Carrier,
      binaryStructuredEpiConstant (A.Carrier ⧸ N.1) ≤ C)
    (L : Family w) (N : NormalAxis A.Carrier) :
    polynomial N L.1 ≤ ((C*(s+2)^C : ℕ) : ℝ) := by
  have hL : Nat.card L.1 ≤ 2^s :=
    (Nat.card_le_card_of_injective L.1.subtype Subtype.coe_injective).trans hcard
  have h := binaryStructured_polynomial_le_uniform (A.Carrier ⧸ N.1)
    (binaryCharacterRank L.1) s C
    (binaryCharacterRank_le_of_card_le_pow L.1 s hL) (hC N)
  dsimp only [polynomial]
  exact_mod_cast h

/-- The exact product weights survive the uniform polynomial estimate.
The suffix sum is the same literal full family, with the shifted marks. -/
theorem markedSum_cons_le_uniform (A : Factor) (w : List Factor)
    (v : AxisWeights (A :: w)) (hv : WeightsNonnegative (A :: w) v)
    (P : Subgroup (Product (A :: w)) → Prop)
    (s C : ℕ) (hcard : Nat.card (Product w) ≤ 2^s)
    (hC : ∀ N : NormalAxis A.Carrier,
      binaryStructuredEpiConstant (A.Carrier ⧸ N.1) ≤ C)
    (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    markedSum (A :: w) v P x y z ≤
      ((C*(s+2)^C : ℕ) : ℝ) *
        ∑ N : NormalAxis A.Carrier, v.1 N * (2 : ℝ)^(cost N x y z) *
          markedSum w v.2 (fun _ => True)
            (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z := by
  let D : ℝ := ((C*(s+2)^C : ℕ) : ℝ)
  calc
    _ ≤ ∑ L : Family w, ∑ N : NormalAxis A.Carrier,
        v.1 N * weight w v.2 L * polynomial N L.1 * (2 : ℝ)^(cost N x y z) *
          mark L.1 (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z :=
      markedSum_cons_le A w v hv P x y z hy hz
    _ ≤ ∑ L : Family w, ∑ N : NormalAxis A.Carrier,
        v.1 N * weight w v.2 L * D * (2 : ℝ)^(cost N x y z) *
          mark L.1 (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z := by
      apply Finset.sum_le_sum
      intro L _
      apply Finset.sum_le_sum
      intro N _
      apply mul_le_mul_of_nonneg_right _ (mark_nonneg L.1 _ _ _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
      exact mul_le_mul_of_nonneg_left (tail_polynomial_le A w s C hcard hC L N)
        (mul_nonneg (hv.1 N) (weight_nonneg w v.2 hv.2 L))
    _ = _ := by
      rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _
      simp only [markedSum,if_true,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro L _
      dsimp only [D]
      ring

/-- Empty products have one subgroup and the exact mark one, including
the actual terminal inflation kernel. An arbitrary survival test can only
remove that subgroup. -/
theorem markedSum_nil_le (v : AxisWeights [])
    (P : Subgroup (Product []) → Prop) (x y z : ℝ) :
    markedSum [] v P x y z ≤ 1 := by
  letI : Subsingleton (Product []) := inferInstanceAs (Subsingleton PUnit.{1})
  letI : Subsingleton (Subgroup (Product [])) := Subgroup.subsingleton_iff.mpr inferInstance
  have hc : Fintype.card (Family []) = 1 :=
    Fintype.card_eq_one_of_forall_eq (i := ⟨⊤,full_nil ⊤⟩)
      (fun H => Subsingleton.elim H _)
  calc
    _ ≤ ∑ _H : Family [], (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro H _
      split_ifs
      · simp only [weight,mark_eq_one_of_subsingleton,mul_one,le_refl]
      · exact zero_le_one
    _ = 1 := by simp only [Finset.sum_const,Finset.card_univ,hc,one_smul]

/-- Induction on the actual word proves the normal-history envelope.
The input bounds concern actual orders and target constants, never the
subgroup sum being bounded. Every quotient slope remains unchanged. -/
theorem markedSum_le_history (w : List Factor) :
    ∀ (v : AxisWeights w), WeightsNonnegative w v →
    ∀ (P : Subgroup (Product w) → Prop) (s C : ℕ),
      Nat.card (Product w) ≤ 2^s → TargetConstants w C →
    ∀ (x y z : ℝ), 0 ≤ y → 0 ≤ z →
      markedSum w v P x y z ≤
        (((C*(s+2)^C : ℕ) : ℝ)^w.length) * normalHistorySum w v x y z := by
  induction w with
  | nil =>
      intro v hv P s C hcard hC x y z hy hz
      simpa only [List.length_nil,pow_zero,normalHistorySum,mul_one] using
        markedSum_nil_le v P x y z
  | cons A w ih =>
      intro v hv P s C hcard hC x y z hy hz
      let D : ℝ := ((C*(s+2)^C : ℕ) : ℝ)
      have hD : 0 ≤ D := Nat.cast_nonneg _
      have htail : Nat.card (Product w) ≤ 2^s := (tail_card_le A w).trans hcard
      calc
        _ ≤ D * ∑ N : NormalAxis A.Carrier,
            v.1 N * (2 : ℝ)^(cost N x y z) *
              markedSum w v.2 (fun _ => True)
                (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z :=
          markedSum_cons_le_uniform A w v hv P s C htail hC.1 x y z hy hz
        _ ≤ D * ∑ N : NormalAxis A.Carrier,
            v.1 N * (2 : ℝ)^(cost N x y z) *
              (D^w.length * normalHistorySum w v.2
                (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z) := by
          apply mul_le_mul_of_nonneg_left _ hD
          apply Finset.sum_le_sum
          intro N _
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (hv.1 N) (Real.rpow_nonneg (by norm_num) _))
          exact ih v.2 hv.2 (fun _ => True) s C htail hC.2 _ _ z
            (add_nonneg hy (Nat.cast_nonneg _)) hz
        _ = _ := by
          simp only [normalHistorySum,List.length_cons,pow_succ,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro N _
          dsimp only [D]
          ring

end BinaryCarrierWord
end SymmetricSubgroupAsymptotics
