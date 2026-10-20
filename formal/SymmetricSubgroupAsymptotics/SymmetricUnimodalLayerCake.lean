import SymmetricSubgroupAsymptotics.CentralBinomialPeakedness

/-! An integral layer-cake decomposition of a symmetric unimodal finite
sequence into nonnegative centered interval indicators. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

structure SymmetricUnimodal (n : ℕ) (f : ℕ → ℕ) : Prop where
  symmetric : ∀ i, i≤n → f (n-i)=f i
  monotone_left : ∀ a b, a≤b → b≤n/2 → f a≤f b

namespace SymmetricUnimodal

variable {n : ℕ} {f : ℕ → ℕ} (h : SymmetricUnimodal n f)

def increment (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | a+1 => f (a+1)-f a

include h in
theorem sum_increments (b : ℕ) : b≤n/2 →
    (∑ a∈Finset.range (b+1),increment f a)=f b := by
  induction b with
  | zero => intro _; simp [increment]
  | succ b ih =>
    intro hb
    rw [Finset.sum_range_succ,ih (by omega)]
    change f b+(f (b+1)-f b)=f (b+1)
    have hm := h.monotone_left b (b+1) (by omega) hb
    omega

include h in
theorem value_eq_distance (i : ℕ) (hi : i≤n) : f i=f (min i (n-i)) := by
  by_cases hmin : i≤n-i
  · rw [Nat.min_eq_left hmin]
  · rw [Nat.min_eq_right (by omega)]
    exact (h.symmetric i hi).symm

include h in
/-- Every coefficient is the sum of centered-layer increments containing
its original index; all increments are natural numbers. -/
theorem layer_cake (i : ℕ) (hi : i≤n) :
    f i=∑ a∈Finset.range (n/2+1),
      if a≤i ∧ i≤n-a then increment f a else 0 := by
  let d := min i (n-i)
  have hd : d≤n/2 := by dsimp [d]; omega
  have hsub : Finset.range (d+1)⊆Finset.range (n/2+1) := Finset.range_mono (by omega)
  calc
    f i=f d := h.value_eq_distance i hi
    _ = ∑ a∈Finset.range (d+1),increment f a := (h.sum_increments d hd).symm
    _ = ∑ a∈Finset.range (d+1),if a≤i ∧ i≤n-a then increment f a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have had : a≤d := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      have hc : a≤i ∧ i≤n-a := by dsimp [d] at had; omega
      rw [if_pos hc]
    _ = ∑ a∈Finset.range (n/2+1),if a≤i ∧ i≤n-a then increment f a else 0 := by
      apply Finset.sum_subset hsub
      intro a ha hnot
      have ha0 := Finset.mem_range.mp ha
      have had : ¬a<d+1 := fun had => hnot (Finset.mem_range.mpr had)
      have hc : ¬(a≤i ∧ i≤n-a) := by dsimp [d] at had; omega
      exact if_neg hc

include h in
/-- Weighted sums are nonnegative combinations of centered interval
masses, with the same original weight sequence on both sides. -/
theorem weighted_sum_eq (g : Fin (n+1) → ℕ) :
    (∑ i, f i.val*g i)=∑ a∈Finset.range (n/2+1), increment f a*
      ∑ i∈CentralBinomialPeakedness.centralSlice n a,g i := by
  calc
    (∑ i, f i.val*g i)=∑ i : Fin (n+1),
        (∑ a∈Finset.range (n/2+1),if a≤i.val ∧ i.val≤n-a then increment f a else 0)*g i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [h.layer_cake i.val (Nat.le_of_lt_succ i.isLt)]
    _ = ∑ a∈Finset.range (n/2+1), ∑ i : Fin (n+1),
        (if a≤i.val ∧ i.val≤n-a then increment f a else 0)*g i := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∑ a∈Finset.range (n/2+1), increment f a*
        ∑ i∈CentralBinomialPeakedness.centralSlice n a,g i := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [CentralBinomialPeakedness.centralSlice,Finset.sum_filter,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp

include h in
/-- Central mass comparison is preserved when tested against any
symmetric unimodal nonnegative sequence. -/
theorem weighted_mass_le (g q : Fin (n+1) → ℕ) (r s : ℕ)
    (hmass : ∀ a : ℕ,
      r*(∑ i∈CentralBinomialPeakedness.centralSlice n a,g i)≤
        s*(∑ i∈CentralBinomialPeakedness.centralSlice n a,q i)) :
    r*(∑ i, f i.val*g i)≤s*(∑ i,f i.val*q i) := by
  rw [h.weighted_sum_eq g,h.weighted_sum_eq q,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  calc
    r*(increment f a*∑ i∈CentralBinomialPeakedness.centralSlice n a,g i)=
        increment f a*(r*∑ i∈CentralBinomialPeakedness.centralSlice n a,g i) := by ring
    _ ≤ increment f a*(s*∑ i∈CentralBinomialPeakedness.centralSlice n a,q i) :=
      Nat.mul_le_mul_left _ (hmass a)
    _ = s*(increment f a*∑ i∈CentralBinomialPeakedness.centralSlice n a,q i) := by ring

end SymmetricUnimodal
end SymmetricSubgroupAsymptotics
