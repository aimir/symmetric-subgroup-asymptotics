import SymmetricSubgroupAsymptotics.CharacteristicChiefPrimePowerCosts

/-! Automatic order control on the ACTUAL characteristic profile.
The selected q-dimension retains its q-power; every other prime is at
least two, and genuine simple-rank charges keep their proved 2-powers.
No numerical budget is supplied by the caller. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CharacteristicChiefOrderProductBound
open ActualWreathCharacteristicChiefProfile CharacteristicChiefFilteredDimensions
open CharacteristicChiefPrimePowerCosts

theorem mixed_order_product_le {t : ℕ} (L : List (ElementaryCharge t)) (q : ℕ) :
    q ^ dimensionAt q L * 2 ^ otherDimensionAt q L ≤
      (L.map (fun c => c.p ^ c.dimension)).prod := by
  induction L with
  | nil => simp [dimensionAt, otherDimensionAt]
  | cons c L ih =>
      by_cases hc : c.p = q
      · simp only [dimensionAt, otherDimensionAt, if_pos hc, List.map_cons, List.prod_cons]
        calc
          q ^ (c.dimension + dimensionAt q L) * 2 ^ otherDimensionAt q L =
              q ^ c.dimension * (q ^ dimensionAt q L * 2 ^ otherDimensionAt q L) := by
            rw [pow_add]
            ac_rfl
          _ ≤ q ^ c.dimension * (L.map (fun c => c.p ^ c.dimension)).prod :=
            Nat.mul_le_mul_left _ ih
          _ = c.p ^ c.dimension * (L.map (fun c => c.p ^ c.dimension)).prod := by rw [hc]
      · simp only [dimensionAt, otherDimensionAt, if_neg hc, List.map_cons, List.prod_cons]
        calc
          q ^ dimensionAt q L * 2 ^ (c.dimension + otherDimensionAt q L) =
              2 ^ c.dimension * (q ^ dimensionAt q L * 2 ^ otherDimensionAt q L) := by
            rw [pow_add]
            ac_rfl
          _ ≤ c.p ^ c.dimension * (L.map (fun c => c.p ^ c.dimension)).prod :=
            Nat.mul_le_mul (Nat.pow_le_pow_left c.prime.two_le _) ih

theorem profile_mixed_order_le {t cost localOrder : ℕ}
    (P : Profile t cost localOrder) (q : ℕ) :
    q ^ dimensionAt q P.charges * 2 ^ (otherDimensionAt q P.charges + P.simpleRank) ≤
      localOrder := by
  calc
    _ = (q ^ dimensionAt q P.charges * 2 ^ otherDimensionAt q P.charges) *
        2 ^ P.simpleRank := by rw [pow_add]; ac_rfl
    _ ≤ (P.charges.map (fun c => c.p ^ c.dimension)).prod * 2 ^ P.simpleRank :=
      Nat.mul_le_mul_right _ (mixed_order_product_le P.charges q)
    _ ≤ localOrder := P.order_bound

theorem other_dimensions_rank_two_pow_le_order {t cost localOrder : ℕ}
    (P : Profile t cost localOrder) (q : ℕ) (hq : q.Prime) :
    2 ^ (otherDimensionAt q P.charges + P.simpleRank) ≤ localOrder := by
  have hp : 1 ≤ q ^ dimensionAt q P.charges :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hq.ne_zero)
  calc
    _ = 1 * 2 ^ (otherDimensionAt q P.charges + P.simpleRank) := (one_mul _).symm
    _ ≤ q ^ dimensionAt q P.charges *
        2 ^ (otherDimensionAt q P.charges + P.simpleRank) := Nat.mul_le_mul_right _ hp
    _ ≤ localOrder := profile_mixed_order_le P q

theorem other_dimensions_rank_le_log_order {t cost localOrder : ℕ}
    (P : Profile t cost localOrder) (q : ℕ) (hq : q.Prime) :
    (otherDimensionAt q P.charges : ℝ) + P.simpleRank ≤ Real.logb 2 (localOrder : ℝ) := by
  have hp : (2 : ℝ) ^ (otherDimensionAt q P.charges + P.simpleRank) ≤ localOrder := by
    exact_mod_cast other_dimensions_rank_two_pow_le_order P q hq
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num : (0 : ℝ) < 2) _) hp
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one, Nat.cast_add] using hl

end SymmetricSubgroupAsymptotics.CharacteristicChiefOrderProductBound
