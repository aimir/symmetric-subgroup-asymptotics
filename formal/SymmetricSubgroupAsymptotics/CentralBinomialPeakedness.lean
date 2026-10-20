import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

/-! The single-chain comparison for normalized mixed-grid widths:
centered binomial mass is at least centered uniform mass. All statements
are integral, so no division or approximation enters the comparison. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CentralBinomialPeakedness

/-- A subset whose values dominate every outside value has average at
least the average over the whole finite set. -/
theorem average_mass_le {I : Type} [Fintype I] (f : I → ℕ) (s : Finset I)
    (hdom : ∀ i∈s, ∀ j∉s, f j≤f i) :
    s.card*(∑ i, f i)≤Fintype.card I*(∑ i∈s, f i) := by
  have hcross : s.card*(∑ j∈sᶜ,f j)≤sᶜ.card*(∑ i∈s,f i) := by
    calc
      s.card*(∑ j∈sᶜ,f j)=∑ j∈sᶜ,∑ _i∈s,f j := by simp [Finset.mul_sum,Nat.mul_comm]
      _ ≤ ∑ _j∈sᶜ,∑ i∈s,f i := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro i hi
        exact hdom i hi j (Finset.mem_compl.mp hj)
      _ = sᶜ.card*(∑ i∈s,f i) := by simp
  have hcard := Finset.card_add_card_compl s
  have hsum := Finset.sum_add_sum_compl s f
  rw [←hsum,←hcard,Nat.mul_add,Nat.add_mul]
  exact Nat.add_le_add_left hcross _

theorem choose_monotone_left_half (n a b : ℕ) (hab : a≤b) :
    b≤n/2 → n.choose a≤n.choose b := by
  induction b,hab using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ b hab ih =>
    intro hb
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem choose_eq_at_distance (n i : ℕ) (hi : i≤n) :
    n.choose i=n.choose (min i (n-i)) := by
  by_cases h : i≤n-i
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega)]
    exact (Nat.choose_symm hi).symm

def centralSlice (n a : ℕ) : Finset (Fin (n+1)) :=
  Finset.univ.filter (fun i => a≤i.val ∧ i.val≤n-a)

/-- Every coefficient in a centered interval dominates every coefficient
outside that interval, by symmetry and monotonicity toward the middle. -/
theorem centralSlice_dominates (n a : ℕ) :
    ∀ i∈centralSlice n a, ∀ j∉centralSlice n a, n.choose j.val≤n.choose i.val := by
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' : ¬(a≤j.val ∧ j.val≤n-a) := by
    intro h
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hiN : i.val≤n := Nat.le_of_lt_succ i.isLt
  have hjN : j.val≤n := Nat.le_of_lt_succ j.isLt
  rw [choose_eq_at_distance n j.val hjN,choose_eq_at_distance n i.val hiN]
  apply choose_monotone_left_half
  · omega
  · omega

/-- Uniform mass on a chain is no more centrally concentrated than the
binomial distribution of the same total rank. -/
theorem centralSlice_mass (n a : ℕ) :
    (centralSlice n a).card*2^n≤(n+1)*(∑ i∈centralSlice n a,n.choose i.val) := by
  have h := average_mass_le (fun i : Fin (n+1) => n.choose i.val)
    (centralSlice n a) (centralSlice_dominates n a)
  have hsum : (∑ i : Fin (n+1),n.choose i.val)=2^n := by
    rw [Fin.sum_univ_eq_sum_range,Nat.sum_range_choose]
  simpa only [Fintype.card_fin,hsum] using h

end SymmetricSubgroupAsymptotics.CentralBinomialPeakedness
