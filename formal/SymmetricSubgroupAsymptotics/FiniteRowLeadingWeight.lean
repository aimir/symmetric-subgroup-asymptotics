import Mathlib.Data.Finset.Max
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Lattice.Fold

/-! Vector-valued leading rows and the natural weight used for actual
module generators. Zero has weight zero, so cancellation may delete a
generator without requiring the new vector to remain nonzero. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteRowLeadingWeight

variable {V : Type*} [AddCommGroup V] {n : ℕ}

def HasLeading (f : Fin n → V) (a : Fin n) : Prop :=
  f a≠0 ∧ ∀ b : Fin n, a<b → f b=0

def weight (f : Fin n → V) : ℕ :=
  (Finset.univ.filter (fun i => f i≠0)).sup (fun i => i.val+1)

theorem exists_leading {f : Fin n → V} (hf : f≠0) : ∃ a, HasLeading f a := by
  have hs : (Finset.univ.filter (fun a => f a≠0)).Nonempty := by
    by_contra h
    apply hf
    funext a
    by_contra ha
    exact h ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
  let s := Finset.univ.filter (fun a => f a≠0)
  refine ⟨s.max' hs,(Finset.mem_filter.mp (s.max'_mem hs)).2,?_⟩
  intro b hb
  by_contra hbn
  exact (not_lt_of_ge (s.le_max' b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbn⟩))) hb

@[simp] theorem weight_zero : weight (0 : Fin n → V)=0 := by
  simp only [weight,Pi.zero_apply,ne_eq,not_true_eq_false,Finset.filter_false,Finset.sup_empty,Nat.bot_eq_zero]

theorem weight_eq_of_leading {f : Fin n → V} {a : Fin n} (ha : HasLeading f a) :
    weight f=a.val+1 := by
  unfold weight
  apply le_antisymm
  · apply Finset.sup_le
    intro b hb
    have hbn := (Finset.mem_filter.mp hb).2
    have hba : b≤a := by
      by_contra h
      exact hbn (ha.2 b (lt_of_not_ge h))
    exact Nat.add_le_add_right hba 1
  · exact Finset.le_sup (f := fun i : Fin n => i.val+1)
      (s := Finset.univ.filter (fun i => f i≠0))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha.1⟩)

/-- A vector with zero rows at and above a has weight at most a.val,
including the zero vector. -/
theorem weight_le_of_zero_above (f : Fin n → V) (a : Fin n)
    (ha : f a=0) (habove : ∀ b : Fin n, a<b → f b=0) : weight f≤a.val := by
  unfold weight
  apply Finset.sup_le
  intro b hb
  have hbn := (Finset.mem_filter.mp hb).2
  have hba : b<a := by
    rcases lt_trichotomy b a with h|h|h
    · exact h
    · exact False.elim (hbn (by simpa only [h] using ha))
    · exact False.elim (hbn (habove b h))
  exact Nat.succ_le_of_lt hba

/-- Equality of the full vector-valued leading coefficient gives strict
weight reduction, with no choice of fibre basis or nonzero remainder. -/
theorem cancellation_decreases_weight {f g : Fin n → V} {a : Fin n}
    (hf : HasLeading f a) (hg : HasLeading g a) (he : f a=g a) :
    weight (g-f)<weight g := by
  have hzero : (g-f) a=0 := by simp only [Pi.sub_apply,he,sub_self]
  have habove : ∀ b : Fin n, a<b → (g-f) b=0 := by
    intro b hb
    simp only [Pi.sub_apply,hf.2 b hb,hg.2 b hb,sub_self]
  have hle := weight_le_of_zero_above (g-f) a hzero habove
  rw [weight_eq_of_leading hg]
  omega

end SymmetricSubgroupAsymptotics.FiniteRowLeadingWeight
