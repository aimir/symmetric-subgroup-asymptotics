import SymmetricSubgroupAsymptotics.ActualWreathChiefOrderDivisibility

/-! Filtered characteristic dimensions and capacity sums of the actual
chief charge list. Divisibility, not a mere cardinal inequality, bounds
each prime dimension by the true local-order valuation. The same least
capacities retain both the half and real logarithmic estimates. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CharacteristicChiefFilteredDimensions
open ActualWreathCharacteristicChiefProfile ActualWreathChiefOrderDivisibility

def dimensionAt {t : ℕ} (p : ℕ) : List (ElementaryCharge t) → ℕ
  | [] => 0
  | c :: L => if c.p = p then c.dimension + dimensionAt p L else dimensionAt p L

def capacityAt {t : ℕ} (p : ℕ) : List (ElementaryCharge t) → ℕ
  | [] => 0
  | c :: L => if c.p = p then c.capacity + capacityAt p L else capacityAt p L

theorem prime_pow_dimensionAt_dvd {t : ℕ} (L : List (ElementaryCharge t)) (p : ℕ) :
    p ^ dimensionAt p L ∣ (L.map (fun c => c.p ^ c.dimension)).prod := by
  induction L with
  | nil => simp [dimensionAt]
  | cons c L ih =>
      by_cases hc : c.p = p
      · simpa only [dimensionAt, if_pos hc, pow_add, List.map_cons, List.prod_cons, hc, if_true]
          using Nat.mul_dvd_mul (dvd_refl (p ^ c.dimension)) ih
      · simpa only [dimensionAt, if_neg hc, List.map_cons, List.prod_cons, one_mul]
          using Nat.mul_dvd_mul (one_dvd (c.p ^ c.dimension)) ih

theorem dimensionAt_le_factorization {t cost localOrder : ℕ}
    (P : DivisibleProfile t cost localOrder) (p : ℕ) (hp : p.Prime)
    (horder : localOrder ≠ 0) : dimensionAt p P.charges ≤ localOrder.factorization p :=
  (hp.pow_dvd_iff_le_factorization horder).mp
    ((prime_pow_dimensionAt_dvd P.charges p).trans P.elementary_order_dvd)

theorem capacityAt_le_half {t : ℕ} (L : List (ElementaryCharge t)) (p : ℕ) :
    (capacityAt p L : ℝ) ≤ (dimensionAt p L : ℝ) * t / 2 := by
  induction L with
  | nil => simp [dimensionAt, capacityAt]
  | cons c L ih =>
      by_cases hc : c.p = p
      · simpa only [dimensionAt, capacityAt, if_pos hc, Nat.cast_add, add_mul, add_div]
          using add_le_add c.half ih
      · simpa only [dimensionAt, capacityAt, if_neg hc] using ih

theorem capacityAt_le_logarithmic_real {t : ℕ}
    (L : List (ElementaryCharge t)) (p : ℕ) :
    (capacityAt p L : ℝ) ≤
      2 * (dimensionAt p L : ℝ) * t / Real.sqrt (Real.logb 2 (t : ℝ)) := by
  induction L with
  | nil => simp [dimensionAt, capacityAt]
  | cons c L ih =>
      by_cases hc : c.p = p
      · simpa only [dimensionAt, capacityAt, if_pos hc, Nat.cast_add,
          mul_add, add_mul, add_div] using add_le_add c.logarithmic ih
      · simpa only [dimensionAt, capacityAt, if_neg hc] using ih

end SymmetricSubgroupAsymptotics.CharacteristicChiefFilteredDimensions
