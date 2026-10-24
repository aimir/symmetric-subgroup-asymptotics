import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.Index

/-! A center-free group's proper-subgroup index lower bound also controls
its class count. This is a class-equation argument, with no classification
or monotonicity assertion for arbitrary subgroup class counts. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound

variable {G : Type*} [Group G] [Finite G]

theorem class_card_mul_index_le (b : ℕ)
    (hcenter : Subgroup.center G = ⊥)
    (hindex : ∀ H : Subgroup G, H ≠ ⊤ → b ≤ H.index) :
    Nat.card (ConjClasses G) * b ≤ Nat.card G + b := by
  classical
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite (ConjClasses G)
  have hc (c : ConjClasses G) (hc : c ≠ 1) : b ≤ Nat.card c.carrier := by
    obtain ⟨g, rfl⟩ := c.exists_rep
    have hg : g ≠ 1 := by
      intro hg
      exact hc (by simpa [hg] using (ConjClasses.one_eq_mk_one (α := G)).symm)
    have hp : Subgroup.centralizer ({g} : Set G) ≠ ⊤ := by
      intro htop
      have hmem : g ∈ Subgroup.center G :=
        (Subgroup.centralizer_eq_top_iff_subset.mp htop) (by simp : g ∈ ({g} : Set G))
      rw [hcenter, Subgroup.mem_bot] at hmem
      exact hg hmem
    have hcard : Nat.card (ConjClasses.mk g).carrier =
        Nat.card G / Nat.card (Subgroup.centralizer ({g} : Set G)) := by
      simpa only [← Nat.card_eq_fintype_card,
        ← Subgroup.nat_card_centralizer_nat_card_stabilizer] using
        ConjClasses.card_carrier g
    rw [hcard, ← (Subgroup.centralizer ({g} : Set G)).index_mul_card,
      Nat.mul_div_cancel _ (Nat.card_pos (α := Subgroup.centralizer ({g} : Set G)))]
    exact hindex _ hp
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun (c : ConjClasses G) _ => show b ≤ Nat.card c.carrier + (if c = 1 then b else 0) from by
      by_cases h : c = 1
      · simp only [h, ite_true]
        exact Nat.le_add_left _ _
      · simpa only [if_neg h, add_zero] using hc c h)
  have heq : (∑ c : ConjClasses G, Nat.card c.carrier) = Nat.card G := by
    simpa only [Nat.card_eq_fintype_card, Set.toFinset_card] using
      sum_conjClasses_card_eq_card (G := G)
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, Finset.sum_add_distrib, heq,
    Finset.sum_ite_eq', Finset.mem_univ, if_pos] using hsum

theorem class_card_le_div_add_one (b : ℕ) (hb : 0 < b)
    (hcenter : Subgroup.center G = ⊥)
    (hindex : ∀ H : Subgroup G, H ≠ ⊤ → b ≤ H.index) :
    Nat.card (ConjClasses G) ≤ Nat.card G / b + 1 := by
  have h := class_card_mul_index_le b hcenter hindex
  have hd := (Nat.le_div_iff_mul_le hb).mpr h
  simpa only [Nat.add_div_right _ hb] using hd

end SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound
