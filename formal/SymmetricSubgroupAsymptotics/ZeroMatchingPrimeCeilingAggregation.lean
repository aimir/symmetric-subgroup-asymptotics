import SymmetricSubgroupAsymptotics.ZeroMatchingPrimeEnvelopeNumerics

/-! The zero-matching scalar envelope normalized with the actual natural
ceiling. The divisor M<=t pays its additive error one, and both logarithm
comparisons retain the original integer degree. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ZeroMatchingPrimeCeilingAggregation

theorem aggregate_le (d t M : ℕ) (hd1 : 1 ≤ d) (hd6 : d ≤ 6)
    (hM : 64 ≤ M) (hMt : M ≤ t) (C v g : ℝ) (hC0 : 0 ≤ C)
    (hC : C ≤ (d : ℝ)^2) (hv0 : 0 ≤ v) (hvM : v ≤ M)
    (hentropy : Real.logb 2 (t : ℝ) ≤ Real.logb 2 (M : ℝ)+8*v)
    (hcost : g ≤ (t : ℝ)*C/(M : ℝ) +
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  let A := Real.logb 2 (M : ℝ)
  have hMR : (64 : ℝ) ≤ M := by exact_mod_cast hM
  have hMtR : (M : ℝ) ≤ t := by exact_mod_cast hMt
  have hM0 : (0 : ℝ) < M := by linarith
  have ht0 : (0 : ℝ) < t := hM0.trans_le hMtR
  have hA0 : 0 < A := Real.logb_pos (by norm_num) (by linarith : (1 : ℝ) < M)
  have hlower : A ≤ L := Real.logb_le_logb_of_le (by norm_num) hM0 hMtR
  have hL0 : 0 < L := hA0.trans_le hlower
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hcoef0 : 0 ≤ (C+1)/(M : ℝ) := div_nonneg (by linarith) hM0.le
  have hscaled : ((C+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+L) +
      Real.sqrt ((d : ℝ)+L)/Real.sqrt L ≤ (2 : ℝ)^d := by
    have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
      rw [←Real.sqrt_div (by linarith : 0 ≤ (d : ℝ)+L)]
      congr 1
      field_simp [hL0.ne'] <;> ring
    have hrad : (d : ℝ)+L ≤ (d : ℝ)+(A+8*v) :=
      add_le_add (le_rfl : (d : ℝ) ≤ (d : ℝ)) hentropy
    have hfirst : ((C+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+L) ≤
        ((C+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+(A+8*v)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad) hcoef0
    have hratio_le : Real.sqrt (1+(d : ℝ)/L) ≤ Real.sqrt (1+(d : ℝ)/A) :=
      Real.sqrt_le_sqrt (add_le_add (le_rfl : (1 : ℝ) ≤ 1)
        (div_le_div_of_nonneg_left hd0 hA0 hlower))
    rw [hratio]
    apply (add_le_add hfirst hratio_le).trans
    simpa only [A,add_assoc] using
      ZeroMatchingPrimeEnvelopeNumerics.envelope_le M d hM hd1 hd6 C v hC hv0 hvM
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0.le (Real.sqrt_nonneg _))).le
  have hunit : (1 : ℝ) ≤ (t : ℝ)/(M : ℝ) :=
    (le_div_iff₀ hM0).mpr (by simpa using hMtR)
  have hg : g ≤ (t : ℝ)*C/(M : ℝ)+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M : ℝ) := by
    change g ≤ (t : ℝ)*C/(M : ℝ)+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hcost
    linarith only [hcost,hceil,hunit]
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by linarith)
  change g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L)
  apply (le_div_iff₀ hs).mpr
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤
        ((t : ℝ)*C/(M : ℝ)+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M : ℝ))*
          Real.sqrt ((d : ℝ)+L) := mul_le_mul_of_nonneg_right hg hs.le
    _ = (t : ℝ)*(((C+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by ring
    _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled ht0.le
    _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _

end SymmetricSubgroupAsymptotics.ZeroMatchingPrimeCeilingAggregation
