import SymmetricSubgroupAsymptotics.OriginalBinaryAffineCharacteristicCost
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineOrderCost
import SymmetricSubgroupAsymptotics.BinaryAffineDefiningPrimaryTailNumerics
import SymmetricSubgroupAsymptotics.BinaryAffineLargeDimensionWedgeNumerics
import SymmetricSubgroupAsymptotics.TransitiveBinaryGroupOrdinaryRecurrence

/-! An independent original-action induction step, not a proof of the
retained Tracey input. The caller pays only the genuine strictly smaller
top action. Its literal degree is a power of two; no assertion that this
top is a two-group is made. The finite small-dimension/exponent window
is explicit, and no four-point or other finite window is silently paid. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineTraceyWedgeStep
open OriginalAffineBlockCharacteristicHead

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

private theorem top_ceiling_real (e : ℕ)
    (ht : Fintype.card block.Points = 2^e)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    (MarkedC4.genRank block.Top : ℝ) ≤ (2 : ℝ)^e / Real.sqrt e + 1 := by
  have htcard : Nat.card block.Points = 2^e := by
    simpa only [Fintype.card_eq_nat_card] using ht
  have hlog : Real.logb 2 ((2 : ℝ)^e) = (e : ℝ) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  have hc : ((traceyPermutationGeneratorCeiling (Nat.card block.Points) : ℕ) : ℝ) ≤
      (2 : ℝ)^e / Real.sqrt e + 1 := by
    simpa only [traceyPermutationGeneratorCeiling, htcard, Nat.cast_pow,
      Nat.cast_ofNat, hlog] using
      (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (2 : ℝ)^e / Real.sqrt e by positivity)).le
  have hh : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling (Nat.card block.Points) : ℕ) := by exact_mod_cast htop
  exact hh.trans hc

/-- The actual original source fits the coarse constant-one ceiling in
the two proved uniform regions. The top hypothesis is genuinely smaller
by `block.degrees_lt`; it is not inferred from a current-degree input. -/
theorem genRank_le_ceiling (hp : P.p = 2) (e : ℕ) (he : 1 ≤ e)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (hregion : 10 ≤ translationDimension J block P ∨
      (20 ≤ e ∧ 12*translationDimension J block P ≤ e))
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let d := translationDimension J block P
  have hd : 1 ≤ d := by
    have hf := fibre_card_eq_prime_pow_dimension J block P
    have htwo := block.degrees_ge_two.1
    rw [hp] at hf
    by_contra! hh
    have hz : d = 0 := by omega
    change Nat.card block.Fibre = 2^d at hf
    rw [hz, pow_zero] at hf
    omega
  have htopR := top_ceiling_real J block e ht htop
  have hrank : (MarkedC4.genRank J : ℝ)*Real.sqrt ((d+e : ℕ) : ℝ) ≤
      (2 : ℝ)^(d+e) := by
    by_cases hprimary : 20 ≤ e ∧ 12*d ≤ e
    · have hh := OriginalBinaryAffineCharacteristicCost.genRank_le_primary_cost
        J block P hp e ht i
      have htotal : (MarkedC4.genRank J : ℝ) ≤
          ((d : ℝ)*(d+1)/2)*(e.choose (e/2) : ℝ) +
            (2 : ℝ)^e / Real.sqrt e + (d : ℝ)^2 + 1 := by
        change (MarkedC4.genRank J : ℝ) ≤
          ((d : ℝ)*(d+1)/2)*(e.choose (e/2) : ℝ) + (d : ℝ)^2 +
            MarkedC4.genRank block.Top at hh
        linarith
      exact (mul_le_mul_of_nonneg_right htotal (Real.sqrt_nonneg _)).trans
        (BinaryAffineDefiningPrimaryTailNumerics.binary_primary_tail d e hd
          hprimary.1 hprimary.2)
    · have hdlarge : 10 ≤ d := hregion.resolve_right hprimary
      have hew : e ≤ 12*d := by omega
      have hsqrt : (1 : ℝ) ≤ Real.sqrt (e : ℝ) := by
        have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ e by exact_mod_cast he)
        simpa only [Real.sqrt_one] using hh
      have hfrac : (2 : ℝ)^e / Real.sqrt e ≤ (2 : ℝ)^e :=
        div_le_self (by positivity) hsqrt
      have hpow : (1 : ℝ) ≤ (2 : ℝ)^e := one_le_pow₀ (by norm_num)
      have htop2 : (MarkedC4.genRank block.Top : ℝ) ≤ 2*(2 : ℝ)^e := by linarith
      have hh := OriginalBinaryAffineOrderCost.genRank_le_half_order_cost J block P hp i
      have htR : (Nat.card block.Points : ℝ) = (2 : ℝ)^e := by
        exact_mod_cast (show Nat.card block.Points = 2^e by
          simpa only [Fintype.card_eq_nat_card] using ht)
      rw [htR] at hh
      have htotal : (MarkedC4.genRank J : ℝ) ≤
          (((d : ℝ)^2+d)/2+2)*(2 : ℝ)^e := by
        change (MarkedC4.genRank J : ℝ) ≤
          (((d : ℝ)^2+d)/2)*(2 : ℝ)^e + MarkedC4.genRank block.Top at hh
        nlinarith
      exact (mul_le_mul_of_nonneg_right htotal (Real.sqrt_nonneg _)).trans
        (BinaryAffineLargeDimensionWedgeNumerics.half_order_wedge d e hdlarge hew)
  have hn : n = 2^(d+e) := by
    calc
      n = Nat.card block.Fibre * Nat.card block.Points := by
        simpa only [Nat.card_fin] using block.degree_product.symm
      _ = 2^d * 2^e := by
        rw [fibre_card_eq_prime_pow_dimension J block P, hp,
          show Nat.card block.Points = 2^e by
            simpa only [Fintype.card_eq_nat_card] using ht]
      _ = _ := (pow_add _ _ _).symm
  have hspos : 0 < Real.sqrt ((d+e : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hdiv := (le_div_iff₀ hspos).mpr hrank
  have hh := hdiv.trans (Nat.le_ceil ((2 : ℝ)^(d+e)/Real.sqrt ((d+e : ℕ) : ℝ)))
  have hlog : Real.logb 2 ((2 : ℝ)^(d+e)) = (d+e : ℕ) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  have hfinal : (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℕ) := by
    simpa only [traceyPermutationGeneratorCeiling, hn, Nat.cast_pow, Nat.cast_ofNat,
      hlog] using hh
  exact_mod_cast hfinal

theorem exists_generating_finset (hp : P.p = 2) (e : ℕ) (he : 1 ≤ e)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (hregion : 10 ≤ translationDimension J block P ∨
      (20 ≤ e ∧ 12*translationDimension J block P ≤ e))
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨S, hcard, hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S, hgen, hcard.le.trans (genRank_le_ceiling J block P hp e he ht i hregion htop)⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineTraceyWedgeStep
