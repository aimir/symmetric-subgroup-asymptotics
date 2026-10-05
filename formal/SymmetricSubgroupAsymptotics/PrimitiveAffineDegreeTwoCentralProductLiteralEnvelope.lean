import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoCentralProductSummed

/-!
# Literal central-product complete-weight envelope

This is the action-class-free form of the correlated central-repeat row.
It is used when a later affine layer first produces a literal quotient
`Q` and only then recognizes `Q` as `A4 × C2` or `S4 × C2`.  The
complete quotient sum is bounded before any ambient permutation action or
physical pointing is chosen.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PreE7CentralProductRankTailData

variable {Q : Type} [Group Q] [Finite Q]
  (D : PreE7CentralProductRankTailData Q)

/-- The clean exceptional envelope on the literal group. -/
def literalExceptionalEnvelope (b : ℕ) : ℝ :=
  (2 * normalCount D) * ((Nat.factorial b : ℕ) : ℝ) ^ 17 *
    ((2 : ℝ) ^
        (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
      (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))

theorem literalExceptionalEnvelope_nonneg (b : ℕ) :
    0 ≤ D.literalExceptionalEnvelope b := by
  have hs : (0 : ℝ) ≤ subgroupCount (b + 2 * rankTail51Tilt b) := by
    exact_mod_cast (subgroupCount_pos _).le
  unfold literalExceptionalEnvelope
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (normalCount_nonneg D))
      (by positivity)) (mul_nonneg (by positivity) hs)

/-- The joint hot/cold sum on a literal central-product group. -/
theorem literalSummedCompleteWeight_le (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        completeQuotientWeight (R := Q) J) ≤
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
        (normalCount D * completeQuotientWeight (R := Q ⧸ D.E) J +
          (normalCount D * D.lowerConstant) *
            (2 : ℝ) ^ ((3 / 5 : ℝ) * b))) +
        normalCount D * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((1 + Nat.factorial b) *
            ((2 : ℝ) ^
                (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
              (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))) := by
  let hot : Subgroup (Equiv.Perm (Fin b)) → Prop := CentralProductRankHot b
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ hot]
  refine (add_comm _ _).le.trans (add_le_add ?_ ?_)
  · calc
      (∑ J ∈ Finset.univ.filter (fun J => ¬ hot J),
          completeQuotientWeight (R := Q) J) ≤
          ∑ J ∈ Finset.univ.filter (fun J => ¬ hot J),
            (normalCount D * completeQuotientWeight (R := Q ⧸ D.E) J +
              (normalCount D * D.lowerConstant) *
                (2 : ℝ) ^ ((3 / 5 : ℝ) * b)) := by
        apply Finset.sum_le_sum
        intro J hJ
        exact D.completeWeight_cold b J (Finset.mem_filter.mp hJ).2
      _ ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),
            (normalCount D * completeQuotientWeight (R := Q ⧸ D.E) J +
              (normalCount D * D.lowerConstant) *
                (2 : ℝ) ^ ((3 / 5 : ℝ) * b)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro J _ _
        exact add_nonneg
          (mul_nonneg (normalCount_nonneg D) (completeQuotientWeight_nonneg J))
          (mul_nonneg
            (mul_nonneg (normalCount_nonneg D) D.lowerConstant_nonneg)
            (by positivity))
  · calc
      (∑ J ∈ Finset.univ.filter hot,
          completeQuotientWeight (R := Q) J) ≤
          ∑ _J ∈ Finset.univ.filter hot,
            normalCount D * ((Nat.factorial b : ℕ) : ℝ) ^ 16 := by
        apply Finset.sum_le_sum
        intro J _
        exact D.completeWeight_full b J
      _ = normalCount D * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((Finset.univ.filter hot).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ normalCount D * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((1 + Nat.factorial b) *
            ((2 : ℝ) ^
                (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
              (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left (centralProductRankHot_card_le b)
        exact mul_nonneg (normalCount_nonneg D) (by positivity)

theorem literalExceptionalTerm_le_envelope (b : ℕ) :
    normalCount D * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
        ((1 + Nat.factorial b) *
          ((2 : ℝ) ^
              (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
            (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))) ≤
      D.literalExceptionalEnvelope b := by
  have hf : (1 : ℝ) ≤ Nat.factorial b := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero b))
  have htail : 0 ≤
      (2 : ℝ) ^ (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
        (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ) := by
    have hs : (0 : ℝ) ≤ subgroupCount (b + 2 * rankTail51Tilt b) := by
      exact_mod_cast (subgroupCount_pos _).le
    positivity
  unfold literalExceptionalEnvelope
  calc
    _ ≤ normalCount D * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
        ((2 * Nat.factorial b : ℝ) *
          ((2 : ℝ) ^
              (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
            (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right (by linarith) htail
      · exact mul_nonneg (normalCount_nonneg D) (by positivity)
    _ = _ := by ring

/-- Public action-free envelope requested by the degree-three prepend. -/
noncomputable def quotientSummedEnvelope :
    PreE7DegreeTwoPairQuotientSummedEnvelope Q where
  R := Q ⧸ D.E
  mainCoefficient := normalCount D
  coldCoefficient := fun _ => normalCount D * D.lowerConstant
  eta := 0
  theta := 3 / 5
  mainCoefficient_nonneg := normalCount_nonneg D
  coldCoefficient_nonneg := fun _ =>
    mul_nonneg (normalCount_nonneg D) D.lowerConstant_nonneg
  exceptionalRaw := D.literalExceptionalEnvelope
  exceptionalRaw_nonneg := D.literalExceptionalEnvelope_nonneg
  summed := fun b => by
    exact (D.literalSummedCompleteWeight_le b).trans
      (by
        let S : ℝ := ∑ J : Subgroup (Equiv.Perm (Fin b)),
          (normalCount D * completeQuotientWeight (R := Q ⧸ D.E) J +
            (normalCount D * D.lowerConstant) *
              (2 : ℝ) ^ ((3 / 5 : ℝ) * b))
        let T : ℝ := normalCount D * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((1 + Nat.factorial b) *
            ((2 : ℝ) ^
                (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
              (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ)))
        have h : T + S ≤ D.literalExceptionalEnvelope b + S :=
          add_le_add_left (D.literalExceptionalTerm_le_envelope b) S
        have h' : S + T ≤ S + D.literalExceptionalEnvelope b := by
          calc
            S + T = T + S := add_comm _ _
            _ ≤ D.literalExceptionalEnvelope b + S := h
            _ = S + D.literalExceptionalEnvelope b := add_comm _ _
        simpa only [S, T, zero_mul, Real.rpow_zero, one_mul, mul_one] using h')

end PreE7CentralProductRankTailData
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
