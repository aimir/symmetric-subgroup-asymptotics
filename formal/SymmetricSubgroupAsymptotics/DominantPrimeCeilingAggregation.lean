import SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeEnvelope

/-! Normalizing the actual characteristic cost and the natural top
ceiling against the original degree. The ceiling error one is paid by
1/M using the actual M<=t; entropy supplies the two logarithm bounds.
No desired normalized estimate is accepted as a hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DominantPrimeCeilingAggregation
open BinaryAffineDominantPrimeSwitchNumerics

theorem aggregate_le (q a d t : ℕ) (hq : q.Prime) (ha : 512 ≤ a)
    (hd1 : 1 ≤ d) (hd6 : d ≤ 6) (ht : 2 ≤ t) (hMt : q^a ≤ t)
    (C m v g : ℝ) (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ ((d+d*(d-1)/2 : ℕ) : ℝ)) (hv : 0 < v) (hvM : v ≤ (q : ℝ)^a)
    (hentropy : Real.logb 2 (t : ℝ) ≤
      (a : ℝ)*Real.logb 2 (q : ℝ)+8*v)
    (hcost : g ≤ (t : ℝ)*(m*min (rate q a) (1/v)+(C-m)/(q : ℝ)^a) +
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  let A := (a : ℝ)*Real.logb 2 (q : ℝ)
  let M := (q : ℝ)^a
  let B := m*min (rate q a) (1/v)+(C-m)/M
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hM0 : 0 < M := pow_pos (by exact_mod_cast hq.pos) _
  have hL0 : 0 < L := Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < t by omega))
  have hA0 : 0 < A := mul_pos (by exact_mod_cast (show 0 < a by omega))
    (Real.logb_pos (by norm_num) (by exact_mod_cast hq.one_lt))
  have hMtR : M ≤ (t : ℝ) := by dsimp only [M]; exact_mod_cast hMt
  have hlower : A ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hM0 hMtR
    simpa only [M,A,L,Real.logb_pow] using hh
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hsub : 0 ≤ C-m := sub_nonneg.mpr hmC
  have hB0 : 0 ≤ B+1/M := by
    dsimp only [B]
    exact add_nonneg (add_nonneg
      (mul_nonneg hm0 (le_min (Real.sqrt_nonneg _) (div_nonneg zero_le_one hv.le)))
      (div_nonneg hsub hM0.le)) (div_nonneg zero_le_one hM0.le)
  have hscaled : (B+1/M)*Real.sqrt ((d : ℝ)+L) +
      Real.sqrt ((d : ℝ)+L)/Real.sqrt L ≤ (2 : ℝ)^d := by
    have heq : B+1/M = m*min (rate q a) (1/v)+(C-m+1)/M := by dsimp only [B]; ring
    have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
      rw [←Real.sqrt_div (by linarith : 0 ≤ (d : ℝ)+L)]
      congr 1
      field_simp [hL0.ne'] <;> ring
    have hrad : (d : ℝ)+L ≤ (d : ℝ)+(A+8*v) :=
      add_le_add (le_rfl : (d : ℝ) ≤ (d : ℝ)) hentropy
    have hfirst : (B+1/M)*Real.sqrt ((d : ℝ)+L) ≤
        (B+1/M)*Real.sqrt ((d : ℝ)+(A+8*v)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad) hB0
    have hratio_le : Real.sqrt (1+(d : ℝ)/L) ≤ Real.sqrt (1+(d : ℝ)/A) :=
      Real.sqrt_le_sqrt (add_le_add (le_rfl : (1 : ℝ) ≤ 1)
        (div_le_div_of_nonneg_left hd0 hA0 hlower))
    rw [hratio]
    have hh := add_le_add hfirst hratio_le
    rw [heq] at hh ⊢
    apply hh.trans
    simpa only [M,A,add_assoc] using
      BinaryAffineDominantPrimeEnvelope.envelope_le
        q a d hq ha hd1 hd6 C m v hm0 hmC hC hmA hv hvM
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0.le (Real.sqrt_nonneg _))).le
  have hunit : (1 : ℝ) ≤ (t : ℝ)/M := (le_div_iff₀ hM0).mpr (by simpa using hMtR)
  have hg : g ≤ (t : ℝ)*B+(t : ℝ)/Real.sqrt L+(t : ℝ)/M := by
    change g ≤ (t : ℝ)*B+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hcost
    linarith only [hcost,hceil,hunit]
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by linarith)
  change g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L)
  apply (le_div_iff₀ hs).mpr
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤
        ((t : ℝ)*B+(t : ℝ)/Real.sqrt L+(t : ℝ)/M)*Real.sqrt ((d : ℝ)+L) :=
      mul_le_mul_of_nonneg_right hg hs.le
    _ = (t : ℝ)*((B+1/M)*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by ring
    _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled ht0.le
    _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _

end SymmetricSubgroupAsymptotics.DominantPrimeCeilingAggregation
