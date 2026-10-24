import SymmetricSubgroupAsymptotics.CharacteristicChiefPrimePowerCosts
import Mathlib.Data.Finsupp.Order

/-! Joint prime-multiplicity control of the actual elementary charge list.
All characteristics other than a selected prime are counted together.
The input is genuine order divisibility, not an assumed dimension bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CharacteristicChiefPrimeMultiplicityBudget
open ActualWreathCharacteristicChiefProfile ActualWreathChiefOrderDivisibility
open CharacteristicChiefPrimePowerCosts

private def awaySum (q : ℕ) (f : ℕ →₀ ℕ) : ℕ :=
  f.sum (fun p a => if p = q then 0 else a)

private theorem awaySum_mono (q : ℕ) {f g : ℕ →₀ ℕ} (h : f ≤ g) :
    awaySum q f ≤ awaySum q g := by
  apply Finsupp.sum_le_sum_index h
  · intro p _ a b hab
    by_cases hp : p = q
    · simpa only [if_pos hp] using (le_refl (0 : ℕ))
    · simpa only [if_neg hp] using hab
  · intro p _
    split_ifs <;> rfl

private theorem awaySum_add (q : ℕ) (f g : ℕ →₀ ℕ) :
    awaySum q (f + g) = awaySum q f + awaySum q g := by
  exact Finsupp.sum_add_index'
    (fun p => by split_ifs <;> rfl)
    (fun p a b => by split_ifs <;> rfl)

private theorem awaySum_single (q p a : ℕ) :
    awaySum q (Finsupp.single p a) = if p = q then 0 else a := by
  exact Finsupp.sum_single_index (by split_ifs <;> rfl)

def primeMultiplicityAway (q M : ℕ) : ℕ := awaySum q M.factorization

theorem primeMultiplicityAway_mono_of_dvd (q : ℕ) {M N : ℕ}
    (hM : M ≠ 0) (hN : N ≠ 0) (hd : M ∣ N) :
    primeMultiplicityAway q M ≤ primeMultiplicityAway q N :=
  awaySum_mono q ((Nat.factorization_le_iff_dvd hM hN).mpr hd)

theorem primeMultiplicityAway_mul (q : ℕ) {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    primeMultiplicityAway q (M * N) =
      primeMultiplicityAway q M + primeMultiplicityAway q N := by
  unfold primeMultiplicityAway
  rw [Nat.factorization_mul hM hN,awaySum_add]

theorem primeMultiplicityAway_prime_pow (q p a : ℕ) (hp : p.Prime) :
    primeMultiplicityAway q (p ^ a) = if p = q then 0 else a := by
  unfold primeMultiplicityAway
  rw [hp.factorization_pow]
  exact awaySum_single q p a

private theorem elementary_order_ne_zero {t : ℕ} (L : List (ElementaryCharge t)) :
    (L.map (fun c => c.p ^ c.dimension)).prod ≠ 0 := by
  induction L with
  | nil => simp
  | cons c L ih =>
      simp only [List.map_cons,List.prod_cons]
      exact mul_ne_zero (pow_ne_zero c.dimension c.prime.ne_zero) ih

theorem elementary_order_away_eq_otherDimension {t : ℕ}
    (q : ℕ) (L : List (ElementaryCharge t)) :
    primeMultiplicityAway q (L.map (fun c => c.p ^ c.dimension)).prod =
      otherDimensionAt q L := by
  induction L with
  | nil => simp [primeMultiplicityAway,awaySum,otherDimensionAt]
  | cons c L ih =>
      rw [List.map_cons,List.prod_cons,
        primeMultiplicityAway_mul q (pow_ne_zero c.dimension c.prime.ne_zero)
          (elementary_order_ne_zero L),
        primeMultiplicityAway_prime_pow q c.p c.dimension c.prime,ih]
      by_cases hc : c.p = q
      · simp only [otherDimensionAt,if_pos hc,zero_add]
      · simp only [otherDimensionAt,if_neg hc]

theorem otherDimension_le_primeMultiplicityAway {t cost localOrder : ℕ}
    (P : DivisibleProfile t cost localOrder) (q M : ℕ)
    (hM : M ≠ 0) (hd : localOrder ∣ M) :
    otherDimensionAt q P.charges ≤ primeMultiplicityAway q M := by
  rw [← elementary_order_away_eq_otherDimension q P.charges]
  exact primeMultiplicityAway_mono_of_dvd q (elementary_order_ne_zero P.charges) hM
    (P.elementary_order_dvd.trans hd)

end SymmetricSubgroupAsymptotics.CharacteristicChiefPrimeMultiplicityBudget
