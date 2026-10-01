import SymmetricSubgroupAsymptotics.PrimitiveAffineLargeOrderNumerics

/-!
# Catalogue-free SO ownership for large primitive affine actions

The regular elementary-abelian socle of a primitive affine action makes the
point stabilizer faithful on the socle.  The preceding structural file turns
this into the order bound `|L| <= 2^m`, where
`m = (floor(log_2 w) + 1)^2`.  This file pays every literal normal axis and
constructs the actual SO source used by the T1 catalogue.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The logarithmic-square parameter also pays the number of literal normal
axes and the constant coefficient on each of them. -/
theorem primitiveAffine_logSquare_axis_total_bound
    {w : ℕ} (hw : 1024 ≤ w)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (horder : Nat.card U ≤ 2 ^ ((Nat.log 2 w + 1) ^ 2))
    (b : ℕ) :
    fusionAxisEnvelopeTotal U
        (fun _ => (2 : ℝ) ^ ((Nat.log 2 w + 1) ^ 2)) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  letI : Fintype {N : Subgroup U // N.Normal} := Fintype.ofFinite _
  let l := Nat.log 2 w
  let m := (l + 1) ^ 2
  have hw0 : w ≠ 0 := by omega
  have hl10 : 10 ≤ l := by
    dsimp [l]
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    norm_num
    exact hw
  have hnormal : Fintype.card {N : Subgroup U // N.Normal} ≤ 2 ^ (m * m) := by
    rw [Fintype.card_eq_nat_card]
    exact normalSubgroup_card_le_two_pow_sq m
      (by simpa [m, l] using horder)
  have hmenuNat :
      Fintype.card {N : Subgroup U // N.Normal} * 2 ^ m ≤
        2 ^ (m * m + m) := by
    calc
      Fintype.card {N : Subgroup U // N.Normal} * 2 ^ m ≤
          2 ^ (m * m) * 2 ^ m := Nat.mul_le_mul_right _ hnormal
      _ = 2 ^ (m * m + m) := by rw [pow_add]
  have hmlinear : m * m + m ≤ 16 * w := by
    calc
      m * m + m = ((l + 1) ^ 2) ^ 2 + (l + 1) ^ 2 := by simp [m, pow_two]
      _ ≤ 16 * 2 ^ l := succ_sq_sq_add_succ_sq_le_sixteen_pow hl10
      _ ≤ 16 * w := Nat.mul_le_mul_left 16 (Nat.pow_log_le_self 2 hw0)
  have harg : (1024 : ℝ) ≤ ((w + b + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1024 ≤ w + b + 2 by omega)
  have hlogmono : Real.log (1024 : ℝ) ≤
      Real.log ((w + b + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) harg
  have hlogone : (1 : ℝ) ≤ Real.log ((w + b + 2 : ℕ) : ℝ) := by
    have hlogtwo : (1 / 2 : ℝ) < Real.log 2 :=
      lt_trans (by norm_num) Real.log_two_gt_d9
    rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, Real.log_pow] at hlogmono
    norm_num at hlogmono
    simp only [Nat.cast_add, Nat.cast_ofNat] at hlogmono ⊢
    nlinarith
  have hlogSquare : (1 : ℝ) ≤
      Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hexponent : ((m * m + m : ℕ) : ℝ) ≤
      16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2 := by
    have hmlinearR : ((m * m + m : ℕ) : ℝ) ≤ 16 * (w : ℝ) := by
      exact_mod_cast hmlinear
    have hwR : (0 : ℝ) ≤ w := by positivity
    nlinarith
  calc
    fusionAxisEnvelopeTotal U
          (fun _ => (2 : ℝ) ^ ((Nat.log 2 w + 1) ^ 2)) =
        (Fintype.card {N : Subgroup U // N.Normal} : ℝ) *
          (2 : ℝ) ^ ((Nat.log 2 w + 1) ^ 2) := by
      simp [fusionAxisEnvelopeTotal, Finset.sum_const, nsmul_eq_mul]
      exact @Fintype.card_congr
        {N : Subgroup U // N.Normal} {N : Subgroup U // N.Normal}
        (Subtype.fintype Subgroup.Normal) this (Equiv.refl _)
    _ ≤ ((2 ^ (m * m + m) : ℕ) : ℝ) := by
      exact_mod_cast (by simpa [m, l] using hmenuNat)
    _ = (2 : ℝ) ^ ((m * m + m : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num
    _ ≤ (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

namespace Non2UnipotentPrefixFiniteMenu

/-- A primitive affine profile of degree at least `1024` is an actual SO
source, with every normal-axis coefficient paid. -/
noncomputable def primitiveAffineLarge_soOrderSourceData
    {w : ℕ} (U : PreE7NonPairActionClass w) (hw : 1024 ≤ w)
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w)) :
    PreE7SoOrderSourceData w U := by
  let x : Fin w := ⟨0, by omega⟩
  let m := (Nat.log 2 w + 1) ^ 2
  have horder : Nat.card (preE7NonPairAction w U) ≤ 2 ^ m := by
    exact P.card_le_two_pow_logSquare x
  exact
    { width_lower := by omega
      order_not_two_power := U.1.1.representative_not_isPGroup
      m := m
      order_le := horder
      exponent_small := by
        simpa [m] using P.eight_mul_logSquare_le hw
      coefficient_total_bound := fun b =>
        primitiveAffine_logSquare_axis_total_bound hw
          (preE7NonPairAction w U) (by simpa [m] using horder) b }

/-- Catalogue-facing SO source for a large primitive affine action. -/
noncomputable def primitiveAffineLarge_rankTailOwnerSourceData
    {w : ℕ} (U : PreE7NonPairActionClass w) (hw : 1024 ≤ w)
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w)) :
    PreE7RankTailOwnerSourceData w U :=
  .ordinary .so (.semisimple (by
    constructor
    · decide
    · decide) ⟨primitiveAffineLarge_soOrderSourceData U hw P⟩)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
