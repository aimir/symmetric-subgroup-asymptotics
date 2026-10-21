import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! The unmarked tableau energy inequality. This numerical argument uses
real log densities and therefore applies to every prime, without identifying
binary ceiling logarithms or introducing a subgroup-counting hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinaryTableauEnergy

variable {I : Type} [Fintype I] [LinearOrder I]

def energy (c n : I → ℝ) : ℝ :=
  ∑ i : I,∑ j : I,if j<i then (c i-c j)*n i*n j else 0

/-- Every increasing density difference is bounded by its two cross-cut
weights. Summing leaves a product of complementary weighted masses. -/
theorem energy_le_quarter_square (c n : I → ℝ)
    (hc0 : ∀ i,0≤c i) (hc1 : ∀ i,c i≤1) (hn : ∀ i,0≤n i) :
    energy c n≤(∑ i : I,n i)^2/4 := by
  let f : I → I → ℝ := fun i j => c i*(1-c j)*n i*n j
  have hf (i j : I) : 0≤f i j := by
    dsimp [f]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hc0 i) (sub_nonneg.mpr (hc1 j))) (hn i)) (hn j)
  have hpair (i j : I) : (c i-c j)*n i*n j≤f i j+f j i := by
    have hcross := mul_nonneg (hc0 j) (sub_nonneg.mpr (hc1 i))
    have hprod := mul_nonneg (hn i) (hn j)
    dsimp [f]
    nlinarith [mul_nonneg hcross hprod]
  have hsum : energy c n≤
      (∑ i : I,∑ j : I,if j<i then f i j else 0)+
        ∑ i : I,∑ j : I,if j<i then f j i else 0 := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases hji : j<i
    · simpa only [if_pos hji] using hpair i j
    · simp only [if_neg hji,zero_add,le_refl]
  have hswap : (∑ i : I,∑ j : I,if j<i then f j i else 0)=
      ∑ i : I,∑ j : I,if i<j then f i j else 0 := by
    rw [Finset.sum_comm]
  have hbound : energy c n≤∑ i : I,∑ j : I,f i j := by
    apply hsum.trans
    rw [hswap,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    rcases lt_trichotomy j i with hji | hji | hij
    · simp only [hji,not_lt_of_ge hji.le,if_pos,if_false,add_zero]
      exact le_rfl
    · subst j
      simp only [lt_self_iff_false,if_false,zero_add]
      exact hf i i
    · simp only [hij,not_lt_of_ge hij.le,if_pos,if_false,zero_add]
      exact le_rfl
  let A : ℝ := ∑ i : I,c i*n i
  let B : ℝ := ∑ i : I,(1-c i)*n i
  have hAB : (∑ i : I,∑ j : I,f i j)=A*B := by
    dsimp [A,B]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]
    ring
  have htotal : A+B=∑ i : I,n i := by
    dsimp [A,B]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hAB] at hbound
  rw [←htotal]
  nlinarith [sq_nonneg (A-B)]

/-- Uniform original normal ranks multiply the same sharp density energy.
Negative coefficients are never discarded by changing a source rank. -/
theorem ranked_energy_le (c n r : I → ℝ) (d : ℝ)
    (hc0 : ∀ i,0≤c i) (hc1 : ∀ i,c i≤1) (hn : ∀ i,0≤n i)
    (hmono : Monotone c) (hd : 0≤d) (hr : ∀ i,r i≤d*n i) :
    (∑ i : I,∑ j : I,if j<i then (c i-c j)*n j*r i else 0) ≤
      d*(∑ i : I,n i)^2/4 := by
  have hle : (∑ i : I,∑ j : I,if j<i then (c i-c j)*n j*r i else 0) ≤d*energy c n := by
    unfold energy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hji : j<i
    · rw [if_pos hji,if_pos hji]
      have hnon : 0≤(c i-c j)*n j :=
        mul_nonneg (sub_nonneg.mpr (hmono hji.le)) (hn j)
      have h := mul_le_mul_of_nonneg_left (hr i) hnon
      nlinarith
    · simp [hji]
  exact hle.trans (by
    have h := mul_le_mul_of_nonneg_left (energy_le_quarter_square c n hc0 hc1 hn) hd
    nlinarith)

end SymmetricSubgroupAsymptotics.CFSGOrdinaryTableauEnergy
