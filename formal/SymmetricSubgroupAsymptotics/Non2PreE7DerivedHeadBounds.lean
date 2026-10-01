import SymmetricSubgroupAsymptotics.Non2PreE7DerivedHeadCount
import SymmetricSubgroupAsymptotics.PermutationThreeGroupRank

/-!
# Common derived sources inside actual permutation sources

For an actual source `J ≤ S_b`, every derived term `F = J^(n+1)` is again a
faithful permutation group on the same `b` points.  The internally proved
prime-rank bounds therefore give `d₂(F) ≤ b/2` and `d₃(F) ≤ b/3`, and the
two onto counts become exponential in `b`:

* cyclic-dual targets: `|Epi(J, Q)| ≤ |Aut Q| · p^(d_p(F))`;
* common-head targets: `|Epi(J, Q)| ≤ 2 |Aut Q| · q^(d_p(F)/m)`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DerivedHead

/-- Cyclic characters are counted by the prime character rank. -/
theorem card_hom_zmod_eq (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Finite G] :
    Nat.card (G →* Multiplicative (ZMod p)) =
      p ^ Module.finrank (ZMod p) (PrimeCharacters p G) := by
  rw [Nat.card_congr (AddMonoidHom.toMultiplicativeRight (α := G) (β := ZMod p)).symm]
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := PrimeCharacters p G), Nat.card_zmod]

/-- Every subgroup of an actual source has binary rank at most `b/2`. -/
theorem binaryRank_le {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) (F : Subgroup J) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 F) ≤ b / 2 := by
  simpa only [Nat.card_fin] using permutation_binaryCharacterRank_le_half F (Fin b)

/-- Every subgroup of an actual source has ternary rank at most `b/3`. -/
theorem ternaryRank_le {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) (F : Subgroup J) :
    Module.finrank (ZMod 3) (PrimeCharacters 3 F) ≤ b / 3 := by
  simpa only [Nat.card_fin] using permutation_ternaryCharacterRank_le_third F (Fin b)

/-- `p^(⌊b/p⌋) ≤ 2^((log₂ p / p) b)`. -/
theorem pow_floor_div_le_rpow (p b : ℕ) (hp : 1 ≤ p) :
    ((p : ℝ) ^ (b / p) : ℝ) ≤ (2 : ℝ) ^ ((Real.logb 2 p / p) * b) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.logb 2 p := Real.logb_nonneg (by norm_num) (by exact_mod_cast hp)
  have hdiv : ((b / p : ℕ) : ℝ) ≤ (b : ℝ) / p := Nat.cast_div_le
  calc ((p : ℝ) ^ (b / p) : ℝ) = (2 : ℝ) ^ (Real.logb 2 p * ((b / p : ℕ) : ℝ)) := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hp0,
          Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ ((Real.logb 2 p / p) * b) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [div_mul_eq_mul_div, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hdiv hlog

namespace DerivedCyclicTarget

variable {Q : Type*} [Group Q] [Finite Q] {V : Subgroup Q} [V.Normal] {n : ℕ}

/-- Binary cyclic-dual targets: `|Epi(J, Q)| ≤ |Aut Q| · 2^(b/2)`. -/
theorem epi_card_le_binary (D : DerivedCyclicTarget Q V n 2) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (Nat.card (Q ≃* Q) : ℝ) * (2 : ℝ) ^ ((1 / 2 : ℝ) * b) := by
  have h := D.epi_card_le (J := J)
  rw [card_hom_zmod_eq 2] at h
  have hr := binaryRank_le J (derivedSeries J (n + 1))
  have hpow : (2 : ℝ) ^ Module.finrank (ZMod 2) (PrimeCharacters 2 (derivedSeries J (n + 1)))
      ≤ (2 : ℝ) ^ ((1 / 2 : ℝ) * b) := by
    calc (2 : ℝ) ^ Module.finrank (ZMod 2) (PrimeCharacters 2 (derivedSeries J (n + 1)))
        ≤ (2 : ℝ) ^ (b / 2) := pow_le_pow_right₀ (by norm_num) hr
      _ ≤ (2 : ℝ) ^ ((Real.logb 2 2 / 2) * b) := by
          exact_mod_cast pow_floor_div_le_rpow 2 b (by norm_num)
      _ = (2 : ℝ) ^ ((1 / 2 : ℝ) * b) := by
          rw [Real.logb_self_eq_one (by norm_num)]
  calc (Nat.card (GroupEpimorphism J Q) : ℝ)
      ≤ ((2 ^ Module.finrank (ZMod 2) (PrimeCharacters 2 (derivedSeries J (n + 1))) *
          Nat.card (Q ≃* Q) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (Nat.card (Q ≃* Q) : ℝ) *
          (2 : ℝ) ^ Module.finrank (ZMod 2) (PrimeCharacters 2 (derivedSeries J (n + 1))) := by
        push_cast
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)

/-- Ternary cyclic-dual targets: `|Epi(J, Q)| ≤ |Aut Q| · 3^(b/3)`. -/
theorem epi_card_le_ternary (D : DerivedCyclicTarget Q V n 3) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (Nat.card (Q ≃* Q) : ℝ) * (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  have h := D.epi_card_le (J := J)
  rw [card_hom_zmod_eq 3] at h
  have hr := ternaryRank_le J (derivedSeries J (n + 1))
  have hpow : (3 : ℝ) ^ Module.finrank (ZMod 3) (PrimeCharacters 3 (derivedSeries J (n + 1)))
      ≤ (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
    calc (3 : ℝ) ^ Module.finrank (ZMod 3) (PrimeCharacters 3 (derivedSeries J (n + 1)))
        ≤ (3 : ℝ) ^ (b / 3) := pow_le_pow_right₀ (by norm_num) hr
      _ ≤ (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
          exact_mod_cast pow_floor_div_le_rpow 3 b (by norm_num)
  calc (Nat.card (GroupEpimorphism J Q) : ℝ)
      ≤ ((3 ^ Module.finrank (ZMod 3) (PrimeCharacters 3 (derivedSeries J (n + 1))) *
          Nat.card (Q ≃* Q) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (Nat.card (Q ≃* Q) : ℝ) *
          (3 : ℝ) ^ Module.finrank (ZMod 3) (PrimeCharacters 3 (derivedSeries J (n + 1))) := by
        push_cast
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)

end DerivedCyclicTarget

namespace DerivedHeadTarget

variable {Q : Type} [Group Q] [Finite Q] {V : Subgroup Q} [V.Normal] {n m q : ℕ}

/-- Binary common-head targets:
`|Epi(J, Q)| ≤ 2 |Aut Q| · 2^((log₂ q / (2m)) b)`. -/
theorem epi_card_le_binary (D : DerivedHeadTarget 2 Q V n m q) (hq : 2 ≤ q) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (2 * Nat.card (Q ≃* Q) : ℝ) * (2 : ℝ) ^ ((Real.logb 2 q / (2 * m)) * b) := by
  have hm : 0 < m := by
    obtain ⟨χ₀, hχ₀, _⟩ := D.witness
    rw [← D.finrank_eq]
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨χ₀, hχ₀⟩
  set d := Module.finrank (ZMod 2) (PrimeCharacters 2 (derivedSeries J (n + 1)))
  have h := D.epi_card_le (J := J)
  have hgeom := geom_sum_le_two_mul q (d / m) hq
  have hnat : Nat.card (GroupEpimorphism J Q) ≤ 2 * q ^ (d / m) * Nat.card (Q ≃* Q) :=
    h.trans (Nat.mul_le_mul_right _ hgeom)
  have hd : d ≤ b / 2 := binaryRank_le J (derivedSeries J (n + 1))
  have hk : ((d / m : ℕ) : ℝ) ≤ (b : ℝ) / (2 * m) := by
    have h1 : (d / m) * m ≤ b / 2 := (Nat.div_mul_le_self d m).trans hd
    have h2 : ((d / m : ℕ) : ℝ) * m ≤ (b : ℝ) / 2 := by
      have := Nat.cast_div_le (m := b) (n := 2) (α := ℝ)
      have h1' : (((d / m) * m : ℕ) : ℝ) ≤ ((b / 2 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h1' this
      linarith
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog : 0 ≤ Real.logb 2 q := Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ q by omega))
  have hpow : ((q : ℝ) ^ (d / m) : ℝ) ≤ (2 : ℝ) ^ ((Real.logb 2 q / (2 * m)) * b) := by
    calc ((q : ℝ) ^ (d / m) : ℝ) = (2 : ℝ) ^ (Real.logb 2 q * ((d / m : ℕ) : ℝ)) := by
          rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hq0,
            Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ ((Real.logb 2 q / (2 * m)) * b) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          rw [div_mul_eq_mul_div, mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hk hlog
  calc (Nat.card (GroupEpimorphism J Q) : ℝ)
      ≤ ((2 * q ^ (d / m) * Nat.card (Q ≃* Q) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (2 * Nat.card (Q ≃* Q) : ℝ) * (q : ℝ) ^ (d / m) := by
        push_cast
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

end DerivedHeadTarget

end DerivedHead
end SymmetricSubgroupAsymptotics
