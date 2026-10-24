import SymmetricSubgroupAsymptotics.BinaryAffineComplementaryLargeIntervalEnvelope

/-! Actual top-ceiling normalization for the whole complementary-divisor
interval [16,M]. The true ceiling error is paid with M<=t, while the
literal factorization entropy and actual GL coefficient alternatives
supply the checked envelope. No fitted scalar hypothesis is accepted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ComplementaryLargeIntervalCeilingAggregation

theorem aggregate_le (M d t : ℕ) (hM : 64 ≤ M)
    (hd1 : 1 ≤ d) (hd6 : d ≤ 6) (ht : 2 ≤ t) (hMt : M ≤ t)
    (C m v g : ℝ) (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2) (hv : 16 ≤ v) (hvM : v ≤ M)
    (hlog : Real.logb 2 (M : ℝ) ≤ 127 ∨
      (m ≤ (d : ℝ)-1 ∧ Real.logb 2 (M : ℝ) ≤ 635))
    (hentropy : Real.logb 2 (t : ℝ) ≤ Real.logb 2 (M : ℝ)+(17/4)*v)
    (hcost : g ≤ (t : ℝ)*(m/v+(C-m)/(M : ℝ)) +
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  let A := Real.logb 2 (M : ℝ)
  let B := m/v+(C-m)/(M : ℝ)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hL0 : 0 < L := Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < t by omega))
  have hA0 : 0 < A := Real.logb_pos (by norm_num)
    (by exact_mod_cast (show 1 < M by omega))
  have hMtR : (M : ℝ) ≤ t := by exact_mod_cast hMt
  have hlower : A ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hM0 hMtR
    simpa only [A,L] using hh
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hsub : 0 ≤ C-m := sub_nonneg.mpr hmC
  have hB0 : 0 ≤ B+1/(M : ℝ) := by
    dsimp only [B]
    exact add_nonneg (add_nonneg
      (div_nonneg hm0 (by linarith : 0 ≤ v))
      (div_nonneg hsub hM0.le)) (div_nonneg zero_le_one hM0.le)
  have hscaled : (B+1/(M : ℝ))*Real.sqrt ((d : ℝ)+L) +
      Real.sqrt ((d : ℝ)+L)/Real.sqrt L ≤ (2 : ℝ)^d := by
    have heq : B+1/(M : ℝ) = m/v+(C-m+1)/(M : ℝ) := by dsimp only [B]; ring
    have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
      rw [←Real.sqrt_div (by linarith : 0 ≤ (d : ℝ)+L)]
      congr 1
      field_simp [hL0.ne'] <;> ring
    have hrad : (d : ℝ)+L ≤ (d : ℝ)+(A+(17/4)*v) :=
      add_le_add (le_rfl : (d : ℝ) ≤ (d : ℝ)) hentropy
    have hfirst : (B+1/(M : ℝ))*Real.sqrt ((d : ℝ)+L) ≤
        (B+1/(M : ℝ))*Real.sqrt ((d : ℝ)+(A+(17/4)*v)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad) hB0
    have hratio_le : Real.sqrt (1+(d : ℝ)/L) ≤ Real.sqrt (1+(d : ℝ)/A) :=
      Real.sqrt_le_sqrt (add_le_add (le_rfl : (1 : ℝ) ≤ 1)
        (div_le_div_of_nonneg_left hd0 hA0 hlower))
    rw [hratio]
    have hh := add_le_add hfirst hratio_le
    rw [heq] at hh ⊢
    apply hh.trans
    simpa only [A,add_assoc] using
      BinaryAffineComplementaryLargeIntervalEnvelope.envelope_le
        M d hM hd1 hd6 C m v hm0 hmC hC hmA hv hvM hlog
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0.le (Real.sqrt_nonneg _))).le
  have hunit : (1 : ℝ) ≤ (t : ℝ)/(M : ℝ) := (le_div_iff₀ hM0).mpr (by simpa using hMtR)
  have hg : g ≤ (t : ℝ)*B+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M : ℝ) := by
    change g ≤ (t : ℝ)*B+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hcost
    linarith only [hcost,hceil,hunit]
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by linarith)
  change g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L)
  apply (le_div_iff₀ hs).mpr
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤
        ((t : ℝ)*B+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M : ℝ))*Real.sqrt ((d : ℝ)+L) :=
      mul_le_mul_of_nonneg_right hg hs.le
    _ = (t : ℝ)*((B+1/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by ring
    _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled ht0.le
    _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _


end SymmetricSubgroupAsymptotics.ComplementaryLargeIntervalCeilingAggregation
