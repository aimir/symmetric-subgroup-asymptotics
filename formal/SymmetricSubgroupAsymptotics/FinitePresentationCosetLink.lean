import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-! The six actual subgroup-membership rules used by the selected coset
pilot. A Link(u,v) is an ORIGINAL-group statement, not an equality in a
guessed finite table. Right translation preserves a left-coset Link
without assuming the subgroup is normal. Literal free reductions are
checked in the genuine FreeGroup, then evaluated by its universal map. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FinitePresentationCosetLink

variable {ι G : Type*} [Group G]
abbrev Word (ι : Type*) := List (ι × Bool)

def eval (g : ι → G) (w : Word ι) : G := FreeGroup.lift g (FreeGroup.mk w)

@[simp] theorem eval_nil (g : ι → G) : eval g [] = 1 := by
  change FreeGroup.lift g 1 = 1
  exact map_one _

theorem eval_append (g : ι → G) (u v : Word ι) :
    eval g (u ++ v) = eval g u * eval g v := by
  unfold eval
  rw [← FreeGroup.mul_mk,map_mul]

theorem eval_eq_of_reduce_eq [DecidableEq ι] (g : ι → G) (u v : Word ι)
    (h : FreeGroup.reduce u = FreeGroup.reduce v) : eval g u = eval g v :=
  congrArg (FreeGroup.lift g) (FreeGroup.reduce.exact h)

theorem eval_reduce [DecidableEq ι] (g : ι → G) (w : Word ι) :
    eval g (FreeGroup.reduce w) = eval g w :=
  congrArg (FreeGroup.lift g) FreeGroup.reduce.self

def Link (H : Subgroup G) (g : ι → G) (u v : Word ι) : Prop :=
  eval g u * (eval g v)⁻¹ ∈ H

theorem free [DecidableEq ι] (H : Subgroup G) (g : ι → G) (u v : Word ι)
    (h : FreeGroup.reduce u = FreeGroup.reduce v) : Link H g u v := by
  unfold Link
  rw [eval_eq_of_reduce_eq g u v h,mul_inv_cancel]
  exact H.one_mem

theorem subgroup (H : Subgroup G) (g : ι → G) (w : Word ι)
    (h : eval g w ∈ H) : Link H g w [] := by
  simpa only [Link,eval_nil,inv_one,mul_one] using h

theorem relator (H : Subgroup G) (g : ι → G) (r ctx : Word ι)
    (hr : eval g r = 1) : Link H g (ctx ++ r) ctx := by
  unfold Link
  rw [eval_append,hr,mul_one,mul_inv_cancel]
  exact H.one_mem

theorem symm {H : Subgroup G} {g : ι → G} {u v : Word ι}
    (h : Link H g u v) : Link H g v u := by
  have hh := H.inv_mem h
  change eval g v * (eval g u)⁻¹ ∈ H
  simpa only [mul_inv_rev,inv_inv] using hh

theorem trans {H : Subgroup G} {g : ι → G} {u v w : Word ι}
    (h : Link H g u v) (k : Link H g v w) : Link H g u w := by
  have hh := H.mul_mem h k
  change (eval g u * (eval g v)⁻¹) * (eval g v * (eval g w)⁻¹) ∈ H at hh
  simpa only [mul_assoc,inv_mul_cancel_left] using hh

theorem right {H : Subgroup G} {g : ι → G} {u v : Word ι}
    (h : Link H g u v) (w : Word ι) : Link H g (u ++ w) (v ++ w) := by
  unfold Link at h ⊢
  rw [eval_append,eval_append]
  have he : (eval g u * eval g w) * (eval g v * eval g w)⁻¹ =
      eval g u * (eval g v)⁻¹ := by group
  rw [he]
  exact h

/-- Stored endpoints may be canonical reduced words, but all six rules
above continue to refer to the same actual original-group cosets. -/
theorem reduce_endpoints [DecidableEq ι] {H : Subgroup G} {g : ι → G}
    {u v : Word ι} (h : Link H g u v) :
    Link H g (FreeGroup.reduce u) (FreeGroup.reduce v) := by
  simpa only [Link,eval_reduce] using h

end SymmetricSubgroupAsymptotics.FinitePresentationCosetLink
