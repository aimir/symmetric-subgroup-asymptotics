import SymmetricSubgroupAsymptotics.OriginalAffineTameUniformCost
import SymmetricSubgroupAsymptotics.OddAffineTameOrderRealTail
import SymmetricSubgroupAsymptotics.TraceyStrictlySmallerTransitiveActions
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! The independent original odd-affine block step in every local
degree at least128, for arbitrary actual top degree. The translation
head and actual complement quotient are charged separately. The top
ceiling is supplied only at its genuine strictly-smaller degree; the
last theorem derives it from the literal transitive subgroup IH. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalOddAffineTameOrderTail
open OriginalAffineBlockCharacteristicHead TraceyStrictlySmallerTransitiveActions

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_of_local_degree_ge_128 (hp : P.p ≠ 2)
    (hr128 : 128 ≤ Nat.card block.Fibre) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  let d := translationDimension J block P
  let s := Real.logb 2 (r : ℝ)
  let k := Nat.log 2 r
  have hr128' : 128 ≤ r := hr128
  have hr0 : r ≠ 0 := by omega
  have ht : 2 ≤ t := block.degrees_ge_two.2
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : t ≠ 0 := by omega
  have hp3 : 3 ≤ P.p := by have hh := P.p_prime.two_le; omega
  have hlogp : (3/2 : ℝ) ≤ Real.logb 2 (P.p : ℝ) := by
    have hpow := Nat.pow_le_pow_left hp3 2
    have hh := IntegerLogSquareRootCeilingCertificate.log_lower P.p 2 3
      P.p_prime.pos (by decide) ((by decide : 2^3 ≤ 3^2).trans hpow)
    simpa only [Nat.cast_ofNat] using hh
  have hrR : (r : ℝ) = (P.p : ℝ)^d := by
    exact_mod_cast fibre_card_eq_prime_pow_dimension J block P
  have hsDegree : s = (d : ℝ)*Real.logb 2 (P.p : ℝ) := by
    dsimp only [s]
    rw [hrR,Real.logb_pow]
  have hs0 : 0 ≤ s := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ r by omega))
  have hdBound : (d : ℝ) ≤ (2/3)*s := by
    have hh := mul_le_mul_of_nonneg_left hlogp (show (0 : ℝ) ≤ d by positivity)
    rw [← hsDegree] at hh
    linarith only [hh]
  have hk7 : 7 ≤ k := Nat.le_log_of_pow_le (by decide : 1 < 2)
    (show 2^7 ≤ r by simpa only [show (2 : ℕ)^7 = 128 by decide] using hr128')
  have hR : (2 : ℝ)^k ≤ (r : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hr0
  have hsK : s ≤ (k : ℝ)+1 := by
    have hpow : r ≤ 2^(k+1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) r).le
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 (k+1)
      (by omega) (by decide) (by simpa only [pow_one] using hpow)
    simpa only [s,Nat.cast_add,Nat.cast_one,div_one] using hh
  have hcoef : (d : ℝ)*(1+s) ≤ OddAffineTameOrderRealTail.tameCost k := by
    have hfirst := mul_le_mul_of_nonneg_right hdBound (show 0 ≤ 1+s by linarith only [hs0])
    have hprod := mul_le_mul hsK (add_le_add_left hsK 1)
      (show 0 ≤ s+1 by linarith only [hs0]) (show 0 ≤ (k : ℝ)+1 by positivity)
    have hlast := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2/3)
    calc
      (d : ℝ)*(1+s) ≤ ((2/3)*s)*(1+s) := hfirst
      _ = (2/3)*(s*(1+s)) := by ring
      _ ≤ (2/3)*(((k : ℝ)+1)*(1+((k : ℝ)+1))) := by
        simpa only [add_comm] using hlast
      _ = OddAffineTameOrderRealTail.tameCost k := by
        dsimp only [OddAffineTameOrderRealTail.tameCost]
        ring
  have hh := OriginalAffineTameUniformCost.genRank_le_half_cost J block P i
  have hl := OriginalAffineTameUniformCost.genRank_le_log_cost J block P i
  simp only [Fintype.card_eq_nat_card] at hh hl
  change (MarkedC4.genRank J : ℝ) ≤ (d : ℝ)*(1+s)*(t : ℝ)/2+MarkedC4.genRank block.Top at hh
  change (MarkedC4.genRank J : ℝ) ≤ 2*(d : ℝ)*(1+s)*(t : ℝ)/
    Real.sqrt (Real.logb 2 (t : ℝ))+MarkedC4.genRank block.Top at hl
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by exact_mod_cast htop
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hhalf : (MarkedC4.genRank J : ℝ) ≤ OddAffineTameOrderRealTail.tameCost k*(t : ℝ)/2+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hcoef (show (0 : ℝ) ≤ (t : ℝ)/2 by positivity)
    have hcmp : (d : ℝ)*(1+s)*(t : ℝ)/2 ≤ OddAffineTameOrderRealTail.tameCost k*(t : ℝ)/2 := by
      convert hm using 1 <;> ring
    exact hh.trans (add_le_add hcmp htopR)
  have hlog : (MarkedC4.genRank J : ℝ) ≤ 2*OddAffineTameOrderRealTail.tameCost k*(t : ℝ)/
      Real.sqrt (Real.logb 2 (t : ℝ))+
        (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hcoef
      (show (0 : ℝ) ≤ 2*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)) by positivity)
    have hcmp : 2*(d : ℝ)*(1+s)*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)) ≤
        2*OddAffineTameOrderRealTail.tameCost k*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)) := by
      convert hm using 1 <;> ring
    exact hl.trans (add_le_add hcmp htopR)
  have hreal := OddAffineTameOrderRealTail.aggregate_le k hk7 s (r : ℝ) (t : ℝ)
    (MarkedC4.genRank J : ℝ) hs0 hsK hR htR hhalf hlog
  have hn : n = r*t := by simpa only [Nat.card_fin] using block.degree_product.symm
  have hnR : (n : ℝ) = (r : ℝ)*(t : ℝ) := by exact_mod_cast hn
  have hlogn : Real.logb 2 (n : ℝ) = s+Real.logb 2 (t : ℝ) := by
    rw [hnR,Real.logb_mul (by exact_mod_cast hr0) (by exact_mod_cast ht0)]
  have htarget : (MarkedC4.genRank J : ℝ) ≤ (n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ)) := by
    rw [hlogn,hnR]
    exact hreal
  have hfinal := htarget.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hfinal
  exact_mod_cast hfinal

theorem exists_generating_finset_of_smaller_subgroups (hp : P.p ≠ 2)
    (hr128 : 128 ≤ Nat.card block.Fibre) (i : block.Points)
    (hbelow : ∀ (k : ℕ), k < n → ∀ K : Subgroup (Equiv.Perm (Fin k)), 2 ≤ k →
      MulAction.IsPretransitive K (Fin k) →
        ∃ S : Finset K, Subgroup.closure (S : Set K) = ⊤ ∧
          S.card ≤ traceyPermutationGeneratorCeiling k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  have htop := rank_of_faithful_transitive_action n (of_subgroup_generators n hbelow)
    block.Top block.Points block.degrees_ge_two.2
    (by simpa only [Nat.card_fin] using block.degrees_lt.2)
  have hh := genRank_le_ceiling_of_local_degree_ge_128 J block P hp hr128 i htop
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hS.le.trans hh⟩

end SymmetricSubgroupAsymptotics.OriginalOddAffineTameOrderTail
