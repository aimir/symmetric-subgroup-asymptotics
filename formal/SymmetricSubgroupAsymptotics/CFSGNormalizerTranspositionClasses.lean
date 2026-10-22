import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.GroupTheory.Perm.Sign

/-! The intrinsic transposition classes of a permutation subgroup.
Every class supports its full symmetric group inside the original
subgroup, and the original subgroup permutes the classes. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGNormalizerTranspositionClasses
open Equiv
variable {X : Type*} [DecidableEq X] (N : Subgroup (Perm X))

def related (x y : X) : Prop := Equiv.swap x y ∈ N

theorem related_refl (x : X) : related N x x := by
  change Equiv.swap x x ∈ N
  rw [Equiv.swap_self]
  exact N.one_mem

theorem related_symm {x y : X} (h : related N x y) : related N y x := by
  simpa only [related, Equiv.swap_comm] using h

theorem related_trans {x y z : X} (hxy : related N x y) (hyz : related N y z) :
    related N x z := SubmonoidClass.swap_mem_trans N hxy hyz

def pointClass (x : X) : Set X := {y | related N x y}

theorem sameClass_swap_mem {x a b : X} (ha : a ∈ pointClass N x)
    (hb : b ∈ pointClass N x) : Equiv.swap a b ∈ N :=
  related_trans N (related_symm N ha) hb

theorem class_symmetric_range_le [Finite X] (x : X) :
    (Perm.ofSubtype : Perm (pointClass N x) →* Perm X).range ≤ N := by
  have hc : Subgroup.closure {g : Perm (pointClass N x) | Perm.IsSwap g} ≤
      N.comap (Perm.ofSubtype : Perm (pointClass N x) →* Perm X) := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨a, b, hab, rfl⟩
    change Perm.ofSubtype (Equiv.swap a b) ∈ N
    rw [Perm.ofSubtype_swap_eq]
    exact sameClass_swap_mem N a.property b.property
  rw [Perm.closure_isSwap] at hc
  rintro _ ⟨g, rfl⟩
  exact hc (Subgroup.mem_top g)

theorem related_image (g : Perm X) (hg : g ∈ N) {x y : X}
    (hxy : related N x y) : related N (g x) (g y) := by
  have hm := N.mul_mem (N.mul_mem hg hxy) (N.inv_mem hg)
  rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right] at hm
  exact hm

theorem pointClass_image (g : Perm X) (hg : g ∈ N) (x : X) :
    g '' pointClass N x = pointClass N (g x) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact related_image N g hg hy
  · intro hz
    refine ⟨g.symm z, ?_, g.apply_symm_apply z⟩
    have hh := related_image N g⁻¹ (N.inv_mem hg) hz
    change related N (g.symm (g x)) (g.symm z) at hh
    simpa only [g.symm_apply_apply] using hh

theorem classes_eq_or_disjoint (x y : X) :
    pointClass N x = pointClass N y ∨ Disjoint (pointClass N x) (pointClass N y) := by
  by_cases hxy : related N x y
  · left
    ext z
    exact ⟨fun hz => related_trans N (related_symm N hxy) hz,
      fun hz => related_trans N hxy hz⟩
  · right
    apply Set.disjoint_left.mpr
    intro z hx hy
    exact hxy (related_trans N hx (related_symm N hy))

end SymmetricSubgroupAsymptotics.CFSGNormalizerTranspositionClasses
