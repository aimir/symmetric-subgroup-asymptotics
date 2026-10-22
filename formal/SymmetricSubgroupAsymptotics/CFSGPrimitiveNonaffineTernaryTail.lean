import SymmetricSubgroupAsymptotics.CFSGPrimitiveTernaryOrderBounds

/-! The full actual nonaffine degree≥34 three-head tail. Small widths use
only the original full-socle quotient order, not a normal-generator theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGPrimitiveTernaryTailNumerics

private theorem logb_lt_nat_of_lt_pow {ell b : ℕ} (he : 0 < ell)
    (hb : ell < 2^b) : Real.logb 2 ell < b := by
  have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast he : (0 : ℝ) < ell) (by exact_mod_cast hb : (ell : ℝ) < 2^b)
  simpa only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using h

private theorem out_lt_sixty {ell out : ℕ}
    (he : 0 < ell) (hb : ell < 1024) (h : SufficientOuterOrderBudget ell out) :
    out < 60 := by
  have hl := logb_lt_nat_of_lt_pow he (show ell < 2^10 by norm_num; exact hb)
  have ho := h.log_six
  norm_num at hl
  have hr : (out : ℝ) < 60 := by linarith
  exact_mod_cast hr

private theorem out_lt_fifteen {ell out : ℕ}
    (he : 0 < ell) (hb : ell < 27) (h : SufficientOuterOrderBudget ell out) :
    out < 15 := by
  have hl := logb_lt_nat_of_lt_pow he (show ell < 2^5 by norm_num; omega)
  have ho := h.log_three_of_small hb
  norm_num at hl
  have hr : (out : ℝ) < 15 := by linarith
  exact_mod_cast hr

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.relativeThreeHead_strict_smallTail
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds)
    (hf : 34 ≤ Nat.card X) (hs : Nat.card X < 1024)
    (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) < 3*Nat.card X := by
  obtain ⟨ell, _, hell, hd, hb⟩ := D.sufficient_degree_lower hindex
  let k := D.factorCount
  let out := Nat.card (Outer D.Simple)
  let q := Nat.card (G ⧸ finiteGroupSocle G)
  have hdegree : ell^k ≤ Nat.card X := hd
  have hq : q ≤ out^k*k.factorial :=
    CFSGNonaffineCoarseComposition.quotient_card_le_outer_wreath D
  have hhead : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      q.factorization 3 := D.relativeThreeHead_le_quotient_valuation N
  have hq0 : q ≠ 0 := Nat.card_pos.ne'
  have hkpos : 1 ≤ k := D.factorCount_pos
  have hk : k ≤ 4 := by
    by_contra hn
    have hp : 3125 ≤ ell^k := calc
      3125 = 5^5 := by decide
      _ ≤ ell^5 := Nat.pow_le_pow_left hell 5
      _ ≤ ell^k := pow_le_pow_right₀ (by omega : 1 ≤ ell) (by omega)
    omega
  have hellk : ell ≤ ell^k := by
    have hh : ell^1 ≤ ell^k := pow_le_pow_right₀ (by omega : 1 ≤ ell) hkpos
    simpa only [pow_one] using hh
  have hew : ell ≤ Nat.card X := hellk.trans hdegree
  have hout60 : out ≤ 59 := by
    have := out_lt_sixty (by omega : 0 < ell) (by omega) hb
    omega
  have hkcases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  rcases hkcases with hk1 | hk2 | hk3 | hk4
  · rw [hk1] at hq
    norm_num at hq
    have hv : q.factorization 3 ≤ 3 :=
      ternary_factorization_le_of_lt_pow hq0 (by norm_num; omega)
    omega
  · rw [hk2] at hq hdegree
    norm_num at hq
    by_cases he27 : ell < 27
    · have hout : out ≤ 14 := by
        have := out_lt_fifteen (by omega : 0 < ell) he27 hb
        omega
      have hp := Nat.pow_le_pow_left hout 2
      have hv : q.factorization 3 ≤ 5 :=
        ternary_factorization_le_of_lt_pow hq0 (by norm_num at hp ⊢; omega)
      omega
    · have hn : 729 ≤ Nat.card X := (Nat.pow_le_pow_left (show 27 ≤ ell by omega) 2).trans hdegree
      have hp := Nat.pow_le_pow_left hout60 2
      have hv : q.factorization 3 ≤ 8 :=
        ternary_factorization_le_of_lt_pow hq0 (by norm_num at hp ⊢; omega)
      omega
  · rw [hk3] at hq hdegree
    norm_num at hq
    have he27 : ell < 27 := by
      by_contra hn
      have hp := (Nat.pow_le_pow_left (show 27 ≤ ell by omega) 3).trans hdegree
      norm_num at hp
      omega
    have hout : out ≤ 14 := by
      have := out_lt_fifteen (by omega : 0 < ell) he27 hb
      omega
    have hp := Nat.pow_le_pow_left hout 3
    have hn : 125 ≤ Nat.card X := (Nat.pow_le_pow_left hell 3).trans hdegree
    have hv : q.factorization 3 ≤ 8 :=
      ternary_factorization_le_of_lt_pow hq0 (by norm_num at hp ⊢; omega)
    omega
  · rw [hk4] at hq hdegree
    norm_num at hq
    have he27 : ell < 27 := by
      by_contra hn
      have hp := (Nat.pow_le_pow_left (show 27 ≤ ell by omega) 4).trans hdegree
      norm_num at hp
      omega
    have hout : out ≤ 14 := by
      have := out_lt_fifteen (by omega : 0 < ell) he27 hb
      omega
    have hp := Nat.pow_le_pow_left hout 4
    have hn : 625 ≤ Nat.card X := (Nat.pow_le_pow_left hell 4).trans hdegree
    have hv : q.factorization 3 ≤ 12 :=
      ternary_factorization_le_of_lt_pow hq0 (by norm_num at hp ⊢; omega)
    omega

theorem NonaffineData.relativeThreeHead_strict_tail
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds)
    (hf : 34 ≤ Nat.card X) (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) < 3*Nat.card X := by
  by_cases hs : Nat.card X < 1024
  · exact D.relativeThreeHead_strict_smallTail hindex hf hs N
  · exact (Nat.mul_le_mul_left 20 (D.relativeThreeHead_le_logSquare hindex N)).trans_lt
      (quadratic_log_tail (by omega))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
