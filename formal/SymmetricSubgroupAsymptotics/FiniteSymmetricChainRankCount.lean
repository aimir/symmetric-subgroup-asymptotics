import SymmetricSubgroupAsymptotics.FiniteSymmetricChainProduct
import SymmetricSubgroupAsymptotics.ChainMiddleBinomialReplacement
import Mathlib.Data.Fintype.BigOperators

/-! Exact rank counts from a genuine symmetric-chain partition.  These
identities connect the chain-mass comparison to the original finite poset. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteSymmetricChains

variable {I : Type} [Preorder I] [Fintype I] {rank : I → ℕ} {K : ℕ}
    (D : FiniteSymmetricChains I rank K) [Fintype D.Colour]

/-- A rank has exactly one element in each chain whose rank interval
contains it. -/
theorem rank_card (t : ℕ) :
    (Finset.univ.filter (fun x : I => rank x=t)).card =
      ∑ c : D.Colour, if D.start c≤t ∧ t+D.start c≤K then 1 else 0 := by
  have hc : (Finset.univ.filter (fun x : I => rank x=t)).card =
      (Finset.univ.filter (fun c : D.Colour => D.start c≤t ∧ t+D.start c≤K)).card := by
    apply Finset.card_bij (fun x _ => D.colour x)
    · intro x hx
      have hr := (Finset.mem_filter.mp hx).2
      have hb := D.rank_bounds x
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hr] using hb⟩
    · intro x hx y hy hxy
      exact D.rank_unique x y hxy ((Finset.mem_filter.mp hx).2.trans
        (Finset.mem_filter.mp hy).2.symm)
    · intro c hc
      obtain ⟨x,hxc,hxt⟩ := D.rank_surjective c t
        (Finset.mem_filter.mp hc).2.1 (Finset.mem_filter.mp hc).2.2
      exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxt⟩,hxc⟩
  simpa only [Finset.card_eq_sum_ones,Finset.sum_filter] using hc

include D in
/-- The original rank counts are symmetric, including both middle ranks
when the total rank is odd. -/
theorem rank_card_symm (t : ℕ) (ht : t≤K) :
    (Finset.univ.filter (fun x : I => rank x=K-t)).card =
      (Finset.univ.filter (fun x : I => rank x=t)).card := by
  rw [D.rank_card (K-t),D.rank_card t]
  apply Finset.sum_congr rfl
  intro c _
  have he : (D.start c≤K-t ∧ K-t+D.start c≤K) ↔
      (D.start c≤t ∧ t+D.start c≤K) := by omega
  simp only [he]

/-- The number of pairs at a fixed total rank can be counted by the
original chain intervals without changing their underlying points. -/
theorem product_rank_card (m t : ℕ) :
    (Finset.univ.filter (fun a : I×Fin (m+1) => rank a.1+a.2.val=t)).card =
      ∑ i : Fin (m+1), ∑ c : D.Colour,
        if i.val+D.start c≤t ∧ t+D.start c≤i.val+K then 1 else 0 := by
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hit : i.val≤t
  · have hr : (∑ x : I, if rank x+i.val=t then 1 else 0) =
        (Finset.univ.filter (fun x : I => rank x=t-i.val)).card := by
      rw [Finset.card_eq_sum_ones,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      have he : (rank x+i.val=t) ↔ (rank x=t-i.val) := by omega
      simp only [he]
    rw [hr,D.rank_card (t-i.val)]
    apply Finset.sum_congr rfl
    intro c _
    have he : (D.start c≤t-i.val ∧ t-i.val+D.start c≤K) ↔
        (i.val+D.start c≤t ∧ t+D.start c≤i.val+K) := by omega
    simp only [he]
  · have hleft : (∑ x : I, if rank x+i.val=t then 1 else 0)=0 := by
      apply Finset.sum_eq_zero
      intro x _
      exact if_neg (by omega)
    rw [hleft]
    symm
    apply Finset.sum_eq_zero
    intro c _
    exact if_neg (by omega)

/-- Paired middle ranks of the actual product are precisely the weights
used in the binomial replacement inequality. -/
theorem product_middle_pair_card (m : ℕ) :
    (Finset.univ.filter (fun a : I×Fin (m+1) => rank a.1+a.2.val=(K+m)/2)).card +
      (Finset.univ.filter (fun a : I×Fin (m+1) =>
        rank a.1+a.2.val=K+m-(K+m)/2)).card =
      ∑ i : Fin (m+1), ∑ c : D.Colour, middlePairWeight K (D.start c) m i.val := by
  rw [D.product_rank_card m ((K+m)/2),D.product_rank_card m (K+m-(K+m)/2)]
  simp only [middlePairWeight,Finset.sum_add_distrib]

end SymmetricSubgroupAsymptotics.FiniteSymmetricChains
