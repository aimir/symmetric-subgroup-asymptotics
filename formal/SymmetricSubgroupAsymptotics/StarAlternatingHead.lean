import SymmetricSubgroupAsymptotics.LinearJointAnnihilator
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Tactic.Ring

/-! The complete star family of alternating forms on U × k has a
uniform joint-annihilator bound for every actual subspace. A vector with
nonzero last coordinate forces every annihilating parameter to vanish.
Otherwise the problem is exactly the ordinary dual annihilator in U.
No enumeration of subspaces or independent character tuples is used.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k U : Type*} [Field k] [AddCommGroup U] [Module k U]

/-- The star family, with its literal sign convention over any field. -/
def starAlternatingFamily :
    Module.Dual k U →ₗ[k] ((U × k) →ₗ[k] (U × k) →ₗ[k] k) where
  toFun l :=
    { toFun x :=
        { toFun y := l x.1 * y.2 - x.2 * l y.1
          map_add' y z := by
            simp only [Prod.fst_add, Prod.snd_add, map_add]
            ring
          map_smul' c y := by
            simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul,
              RingHom.id_apply]
            ring }
      map_add' x y := by
        apply LinearMap.ext
        intro z
        change l (x + y).1 * z.2 - (x + y).2 * l z.1 =
          (l x.1 * z.2 - x.2 * l z.1) + (l y.1 * z.2 - y.2 * l z.1)
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        ring
      map_smul' c x := by
        apply LinearMap.ext
        intro y
        change l (c • x).1 * y.2 - (c • x).2 * l y.1 =
          c * (l x.1 * y.2 - x.2 * l y.1)
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul]
        ring }
  map_add' l m := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (l x.1 + m x.1) * y.2 - x.2 * (l y.1 + m y.1) =
      (l x.1 * y.2 - x.2 * l y.1) + (m x.1 * y.2 - x.2 * m y.1)
    ring
  map_smul' c l := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (c * l x.1) * y.2 - x.2 * (c * l y.1) =
      c * (l x.1 * y.2 - x.2 * l y.1)
    ring

@[simp] theorem starAlternatingFamily_apply
    (l : Module.Dual k U) (x y : U × k) :
    starAlternatingFamily l x y = l x.1 * y.2 - x.2 * l y.1 := rfl

@[simp] theorem starAlternatingFamily_self
    (l : Module.Dual k U) (x : U × k) :
    starAlternatingFamily l x x = 0 := by
  simp only [starAlternatingFamily_apply, mul_comm (l x.1) x.2, sub_self]

/-- A single vector with nonzero last coordinate kills the entire
joint annihilator, not just its chosen coordinate representatives. -/
theorem starAlternatingFamily_joint_eq_bot_of_last_ne_zero
    (W : Submodule k (U × k)) (w : U × k) (hw : w ∈ W) (ht : w.2 ≠ 0) :
    linearJointAnnihilator (starAlternatingFamily (k := k) (U := U)) W = ⊥ := by
  apply le_antisymm _ bot_le
  intro l hl
  change l = 0
  apply LinearMap.ext
  intro u
  have h := congrArg (fun f : (U × k) →ₗ[k] k => f (u, 0)) (hl w hw)
  have hm : w.2 * l u = 0 := by
    simpa only [starAlternatingFamily_apply, mul_zero, zero_sub,
      LinearMap.zero_apply, neg_eq_zero] using h
  exact (mul_eq_zero.mp hm).resolve_left ht

/-- In the zero-last-coordinate hyperplane, the joint annihilator is
exactly the annihilator of the literal first-coordinate image. -/
theorem starAlternatingFamily_joint_eq_dualAnnihilator
    (W : Submodule k (U × k)) (hW : ∀ w ∈ W, w.2 = 0) :
    linearJointAnnihilator (starAlternatingFamily (k := k) (U := U)) W =
      (W.map (LinearMap.fst k U k)).dualAnnihilator := by
  ext l
  constructor
  · intro hl
    apply (Submodule.mem_dualAnnihilator l).mpr
    intro u hu
    obtain ⟨w, hw, rfl⟩ := hu
    have h := congrArg (fun f : (U × k) →ₗ[k] k => f (0, 1)) (hl w hw)
    simpa only [starAlternatingFamily_apply, map_zero, mul_one, mul_zero,
      sub_zero, LinearMap.zero_apply, LinearMap.fst_apply] using h
  · intro hl w hw
    apply LinearMap.ext
    intro y
    have hlw := ((Submodule.mem_dualAnnihilator l).mp hl) w.1 ⟨w, hw, rfl⟩
    simp only [starAlternatingFamily_apply, hlw, hW w hw, zero_mul,
      sub_zero, LinearMap.zero_apply]

/-- First projection is an actual equivalence on every horizontal
subspace; its injectivity is derived from the zero last coordinate. -/
def starHorizontalEquiv (W : Submodule k (U × k))
    (hW : ∀ w ∈ W, w.2 = 0) : W ≃ₗ[k] W.map (LinearMap.fst k U k) := by
  let f : W →ₗ[k] W.map (LinearMap.fst k U k) :=
    { toFun w := ⟨w.1.1, ⟨w.1, w.2, rfl⟩⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · intro w z hwz
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val hwz
    · exact (hW w.1 w.2).trans (hW z.1 z.2).symm
  · intro z
    obtain ⟨w, hw, he⟩ := z.2
    refine ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    exact he

/-- The complete star family has a uniform dimension bound on every
subspace, including zero and the full space. -/
theorem starAlternatingFamily_finrank_add_joint_le_max [FiniteDimensional k U]
    (W : Submodule k (U × k)) :
    Module.finrank k W +
        Module.finrank k
          (linearJointAnnihilator (starAlternatingFamily (k := k) (U := U)) W) ≤
      max (Module.finrank k U) (Module.finrank k W) := by
  classical
  by_cases h : ∃ w ∈ W, w.2 ≠ 0
  · obtain ⟨w, hw, ht⟩ := h
    rw [starAlternatingFamily_joint_eq_bot_of_last_ne_zero W w hw ht,
      finrank_bot, Nat.add_zero]
    exact le_max_right _ _
  · have hW : ∀ w ∈ W, w.2 = 0 := by
      intro w hw
      by_contra ht
      exact h ⟨w, hw, ht⟩
    rw [starAlternatingFamily_joint_eq_dualAnnihilator W hW,
      (starHorizontalEquiv W hW).finrank_eq,
      Subspace.finrank_add_finrank_dualAnnihilator_eq]
    exact le_max_left _ _

section Transport

variable {L V : Type*} [AddCommGroup L] [Module k L]
    [AddCommGroup V] [Module k V]

/-- A pointwise identity under genuine coordinate equivalences retains
the exact original joint annihilator. This is an equality, not an
assumption that the original characters extend or span a chosen menu. -/
theorem linearJointAnnihilator_eq_comap_star
    (F : L →ₗ[k] (V →ₗ[k] V →ₗ[k] k))
    (eL : L ≃ₗ[k] Module.Dual k U) (eV : V ≃ₗ[k] U × k)
    (hF : ∀ l x y, F l x y = starAlternatingFamily (eL l) (eV x) (eV y))
    (W : Submodule k V) :
    linearJointAnnihilator F W =
      (linearJointAnnihilator (starAlternatingFamily (k := k) (U := U))
        (W.map eV.toLinearMap)).comap eL.toLinearMap := by
  ext l
  constructor
  · intro hl w hw
    obtain ⟨x, hx, rfl⟩ := hw
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := eV.surjective y
    change starAlternatingFamily (eL l) (eV x) (eV z) = 0
    exact (hF l x z).symm.trans
      (congrArg (fun f : V →ₗ[k] k => f z) (hl x hx))
  · intro hl x hx
    apply LinearMap.ext
    intro y
    change F l x y = 0
    exact (hF l x y).trans
      (congrArg (fun f : (U × k) →ₗ[k] k => f (eV y))
        (hl (eV x) ⟨x, hx, rfl⟩))

/-- The same uniform bound for an actual form family identified with
the star family by explicit character and original-space equivalences. -/
theorem linearJointAnnihilator_finrank_add_le_max_of_star [FiniteDimensional k U]
    (F : L →ₗ[k] (V →ₗ[k] V →ₗ[k] k))
    (eL : L ≃ₗ[k] Module.Dual k U) (eV : V ≃ₗ[k] U × k)
    (hF : ∀ l x y, F l x y = starAlternatingFamily (eL l) (eV x) (eV y))
    (W : Submodule k V) :
    Module.finrank k W + Module.finrank k (linearJointAnnihilator F W) ≤
      max (Module.finrank k U) (Module.finrank k W) := by
  let J := linearJointAnnihilator (starAlternatingFamily (k := k) (U := U))
    (W.map eV.toLinearMap)
  have hJ : Module.finrank k (linearJointAnnihilator F W) = Module.finrank k J := by
    rw [linearJointAnnihilator_eq_comap_star F eL eV hF W]
    exact (eL.ofSubmodule' J).finrank_eq
  have h := starAlternatingFamily_finrank_add_joint_le_max (W.map eV.toLinearMap)
  rw [eV.finrank_map_eq] at h
  rw [hJ]
  exact h

end Transport

end SymmetricSubgroupAsymptotics
