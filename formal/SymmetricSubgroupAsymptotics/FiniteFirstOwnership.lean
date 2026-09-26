import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact first-eligible ownership on the original finite objects. The
predicates may retain all earlier exclusions and arbitrary original weights.
Coverage is a literal membership hypothesis, never a numerical bound. This
module does not identify an eligible family for any subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {α β : Type*} {r : ℕ}

/-- Membership in the first eligible complete family, in the specified order. -/
def FirstOwned (P : Fin r → α → Prop) (i : Fin r) (x : α) : Prop :=
  P i x ∧ ∀ j : Fin r, j < i → ¬ P j x

theorem firstOwned_exists (P : Fin r → α → Prop) (x : α)
    (h : ∃ i, P i x) : ∃ i, FirstOwned P i x := by
  let s := Finset.univ.filter (fun i => P i x)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  refine ⟨s.min' hs, (Finset.mem_filter.mp (Finset.min'_mem s hs)).2, ?_⟩
  intro j hj hp
  have hjm : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hp⟩
  exact (not_le_of_gt hj) (Finset.min'_le s j hjm)

theorem firstOwned_unique (P : Fin r → α → Prop) {x : α} {i j : Fin r}
    (hi : FirstOwned P i x) (hj : FirstOwned P j x) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (hj.2 i h hi.1)
  · exact h
  · exact False.elim (hi.2 j h hj.1)

/-- Two-way predicate transport preserves the first owner, including every
prior exclusion. The map need not forget or summarize any original data. -/
theorem firstOwned_transport_iff (P : Fin r → α → Prop) (Q : Fin r → β → Prop)
    (f : α → β) (h : ∀ i x, P i x ↔ Q i (f x)) (i : Fin r) (x : α) :
    FirstOwned P i x ↔ FirstOwned Q i (f x) := by
  constructor
  · rintro ⟨hi, hprev⟩
    exact ⟨(h i x).mp hi, fun j hj hp => hprev j hj ((h j x).mpr hp)⟩
  · rintro ⟨hi, hprev⟩
    exact ⟨(h i x).mpr hi, fun j hj hp => hprev j hj ((h j x).mp hp)⟩

/-- Forgetting the owner retains the exact original object. -/
def firstOwnershipForget (R : α → Prop) (P : Fin r → α → Prop) :
    (Σ i : Fin r, {x : α // R x ∧ FirstOwned P i x}) → {x : α // R x} :=
  fun d => ⟨d.2.1, d.2.2.1⟩

theorem firstOwnershipForget_bijective (R : α → Prop) (P : Fin r → α → Prop)
    (hcover : ∀ x, R x → ∃ i, P i x) :
    Function.Bijective (firstOwnershipForget R P) := by
  constructor
  · rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ he
    have hxy : x = y := congrArg Subtype.val he
    subst y
    have hij := firstOwned_unique P hx.2 hy.2
    subst j
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨i, hi⟩ := firstOwned_exists P x (hcover x hx)
    exact ⟨⟨i, x, hx, hi⟩, rfl⟩

/-- Exact partition of the retained original family, with no duplicate owner. -/
def firstOwnershipEquiv (R : α → Prop) (P : Fin r → α → Prop)
    (hcover : ∀ x, R x → ∃ i, P i x) :
    {x : α // R x} ≃ Σ i : Fin r, {x : α // R x ∧ FirstOwned P i x} :=
  (Equiv.ofBijective (firstOwnershipForget R P)
    (firstOwnershipForget_bijective R P hcover)).symm

@[simp] theorem firstOwnershipEquiv_symm_val
    (R : α → Prop) (P : Fin r → α → Prop)
    (hcover : ∀ x, R x → ∃ i, P i x)
    (d : Σ i : Fin r, {x : α // R x ∧ FirstOwned P i x}) :
    ((firstOwnershipEquiv R P hcover).symm d).1 = d.2.1 := rfl

theorem firstOwnership_card [Finite α] (R : α → Prop) (P : Fin r → α → Prop)
    (hcover : ∀ x, R x → ∃ i, P i x) :
    Nat.card {x : α // R x} =
      ∑ i : Fin r, Nat.card {x : α // R x ∧ FirstOwned P i x} := by
  rw [Nat.card_congr (firstOwnershipEquiv R P hcover)]
  exact Nat.card_sigma

/-- Any original additive weight is preserved before applying local bounds.
No sign assumption, multiplicity factor, or change of normalization occurs. -/
theorem firstOwnership_weighted_sum [Fintype α] {M : Type*} [AddCommMonoid M]
    (R : α → Prop) (P : Fin r → α → Prop)
    (hcover : ∀ x, R x → ∃ i, P i x) (W : α → M) :
    (∑ x : {x : α // R x}, W x.1) =
      ∑ i : Fin r, ∑ x : {x : α // R x ∧ FirstOwned P i x}, W x.1 := by
  have h := (firstOwnershipEquiv R P hcover).symm.sum_comp
    (fun x : {x : α // R x} => W x.1)
  simpa only [firstOwnershipEquiv_symm_val, Fintype.sum_sigma] using h.symm

end SymmetricSubgroupAsymptotics
