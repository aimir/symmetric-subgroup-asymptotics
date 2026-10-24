import SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementCoefficientEnvelope
import SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementCeiling

/-! The natural-ceiling normalization of the literal SAME-order joint
rate. Product divisibility is retained as M*v<=t. This supplies the
actual reciprocal error used by the coefficient theorem; no conclusion
that the scalar bound fits is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementAllCeiling
open OriginalBinaryAffineDominantDivisorCost (totalMultiplicity)
open BinaryGeneralLinearMatchingPrimeMultiplicity

def rate (d q a : ℕ) (v : ℝ) : ℝ :=
  (matchingMultiplicity d q : ℝ)/v+
    ((totalMultiplicity d : ℝ)-(matchingMultiplicity d q : ℝ))/(q : ℝ)^a

theorem aggregate_le (q a v d t : ℕ) (hq : q.Prime) (hd : 1 ≤ d)
    (hv : 5 ≤ v) (hvM : v ≤ q^a) (hM64 : q^a < 64) (hcop : Nat.Coprime (q^a) v)
    (hproduct : q^a*v ≤ t)
    (hentropy : Real.logb 2 (t : ℝ) ≤ Real.logb 2 ((q : ℝ)^a)+(3/2)*(v : ℝ))
    (g : ℝ) (hcost : g ≤ (t : ℝ)*rate d q a (v : ℝ)+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  have hvR : (5 : ℝ) ≤ v := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith only [hvR]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hproductR : (q : ℝ)^a*(v : ℝ) ≤ t := by exact_mod_cast hproduct
  have hvsq : v^2 ≤ t := by
    have hh := Nat.mul_le_mul_right v hvM
    nlinarith only [hh,hproduct]
  have ht25 : 25 ≤ t := by nlinarith only [hvsq,hv]
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hL : 9/2 ≤ L := by
    have htR : (25 : ℝ) ≤ t := by exact_mod_cast ht25
    have hpow : (2 : ℝ)^9 ≤ (t : ℝ)^2 := by
      norm_num
      nlinarith only [sq_nonneg ((t : ℝ)-25),htR]
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ)^9) hpow
    simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hh
    norm_num only [Nat.cast_ofNat] at hh
    change 9/2 ≤ Real.logb 2 (t : ℝ)
    linarith only [hh]
  have hL0 : 0 < L := by linarith only [hL]
  have hscaled := SmallPrimaryLargeComplementCoefficientEnvelope.envelope_le
    q a v d hq hd hv hvM hM64 hcop L hL hentropy
  change (rate d q a (v : ℝ)+1/((q : ℝ)^a*(v : ℝ)))*Real.sqrt ((d : ℝ)+L)+
    Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d at hscaled
  have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ (d : ℝ)+L)]
    congr 1
    field_simp [hL0.ne'] <;> ring
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0.le (Real.sqrt_nonneg _))).le
  have hunit : (1 : ℝ) ≤ (t : ℝ)/((q : ℝ)^a*(v : ℝ)) :=
    (le_div_iff₀ (mul_pos (pow_pos hq0 a) hv0)).mpr
      (by simpa only [one_mul] using hproductR)
  have hg : g ≤ (t : ℝ)*rate d q a (v : ℝ)+(t : ℝ)/Real.sqrt L+
      (t : ℝ)/((q : ℝ)^a*(v : ℝ)) := by
    change g ≤ (t : ℝ)*rate d q a (v : ℝ)+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hcost
    linarith only [hcost,hceil,hunit]
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by positivity)
  have hscaled' : (rate d q a (v : ℝ)+1/((q : ℝ)^a*(v : ℝ)))*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt ((d : ℝ)+L)/Real.sqrt L ≤ (2 : ℝ)^d := by
    rw [hratio]
    exact hscaled
  change g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L)
  apply (le_div_iff₀ hs).mpr
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤
        ((t : ℝ)*rate d q a (v : ℝ)+(t : ℝ)/Real.sqrt L+
          (t : ℝ)/((q : ℝ)^a*(v : ℝ)))*Real.sqrt ((d : ℝ)+L) :=
      mul_le_mul_of_nonneg_right hg hs.le
    _ = (t : ℝ)*((rate d q a (v : ℝ)+1/((q : ℝ)^a*(v : ℝ)))*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by ring
    _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled' ht0.le
    _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _

end SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementAllCeiling
