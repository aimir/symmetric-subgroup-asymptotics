import SymmetricSubgroupAsymptotics.CharacteristicChiefFilteredDimensions

/-! On a literal prime-power top degree q^e, only q-characteristic
elementary dimensions receive the growing binomial charge. Every other
characteristic costs at most its genuine dimension by the prime-to bound
with the ENTIRE top degree. Actual simple-factor ranks remain additive. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CharacteristicChiefPrimePowerCosts
open ActualWreathCharacteristicChiefProfile ActualWreathChiefOrderDivisibility
open CharacteristicChiefFilteredDimensions

def otherDimensionAt {t : ℕ} (q : ℕ) : List (ElementaryCharge t) → ℕ
  | [] => 0
  | c :: L => if c.p = q then otherDimensionAt q L else c.dimension + otherDimensionAt q L

theorem capacity_sum_le_primePower {t : ℕ} (L : List (ElementaryCharge t))
    (q e : ℕ) (hq : q.Prime) (ht : t = q ^ e) :
    ((L.map (·.capacity)).sum : ℝ) ≤
      (dimensionAt q L : ℝ) * t *
        ((e * (q - 1)).choose ((e * (q - 1)) / 2) : ℝ) /
          (2 : ℝ) ^ (e * (q - 1)) + otherDimensionAt q L := by
  induction L with
  | nil => simp [dimensionAt, otherDimensionAt]
  | cons c L ih =>
      by_cases hc : c.p = q
      · have hh := add_le_add (c.primePower q e hq ht) ih
        simpa only [List.map_cons, List.sum_cons, Nat.cast_add,
          dimensionAt, otherDimensionAt, if_pos hc, add_mul, add_div, add_assoc] using hh
      · have hd : q ^ e ∣ t := by rw [ht]
        have hh := c.primeTo q e hq (Ne.symm hc) hd
        have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
        have htR : (t : ℝ) = (q : ℝ) ^ e := by exact_mod_cast ht
        rw [htR, mul_div_cancel_right₀ _ (pow_ne_zero _ hq0)] at hh
        have hsum := add_le_add hh ih
        simp only [List.map_cons, List.sum_cons, Nat.cast_add,
          dimensionAt, otherDimensionAt, if_neg hc] at hsum ⊢
        exact hsum.trans_eq (by ring)

theorem profile_cost_le_primePower {t cost localOrder : ℕ}
    (P : Profile t cost localOrder) (q e : ℕ) (hq : q.Prime) (ht : t = q ^ e) :
    (cost : ℝ) ≤ (dimensionAt q P.charges : ℝ) * t *
      ((e * (q - 1)).choose ((e * (q - 1)) / 2) : ℝ) /
        (2 : ℝ) ^ (e * (q - 1)) + otherDimensionAt q P.charges + P.simpleRank := by
  calc
    (cost : ℝ) = ((P.charges.map (·.capacity)).sum : ℝ) + P.simpleRank := by
      simpa only [Nat.cast_add, Nat.cast_list_sum, List.map_map, Function.comp_apply] using
        congrArg (fun k : ℕ => (k : ℝ)) P.total
    _ ≤ _ := add_le_add (capacity_sum_le_primePower P.charges q e hq ht) le_rfl

theorem profile_cost_le_primePower_valuation {t cost localOrder : ℕ}
    (P : DivisibleProfile t cost localOrder) (q e : ℕ) (hq : q.Prime)
    (ht : t = q ^ e) (horder : localOrder ≠ 0) :
    (cost : ℝ) ≤ (localOrder.factorization q : ℝ) * t *
      ((e * (q - 1)).choose ((e * (q - 1)) / 2) : ℝ) /
        (2 : ℝ) ^ (e * (q - 1)) + otherDimensionAt q P.charges + P.simpleRank := by
  have ha : (dimensionAt q P.charges : ℝ) ≤ localOrder.factorization q := by
    exact_mod_cast dimensionAt_le_factorization P q hq horder
  have hcoeff : (0 : ℝ) ≤ (t : ℝ) *
      ((e * (q - 1)).choose ((e * (q - 1)) / 2) : ℝ) /
        (2 : ℝ) ^ (e * (q - 1)) := by positivity
  have hh := mul_le_mul_of_nonneg_right ha hcoeff
  have hm : (dimensionAt q P.charges : ℝ) * t *
      ((e * (q - 1)).choose ((e * (q - 1)) / 2) : ℝ) /
        (2 : ℝ) ^ (e * (q - 1)) ≤
      (localOrder.factorization q : ℝ) * t *
        ((e * (q - 1)).choose ((e * (q - 1)) / 2) : ℝ) /
          (2 : ℝ) ^ (e * (q - 1)) := by
    simpa only [mul_div_assoc, mul_assoc] using hh
  exact (profile_cost_le_primePower P.toProfile q e hq ht).trans
    (add_le_add (add_le_add hm le_rfl) le_rfl)

end SymmetricSubgroupAsymptotics.CharacteristicChiefPrimePowerCosts
