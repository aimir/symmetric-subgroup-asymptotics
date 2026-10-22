import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! Actual integer norm-two vectors and their reflection permutations.
This is the first algebraic part of a simply-laced lattice root system;
finiteness, positive definiteness, a base, and a named Cartan matrix are
not assumed to have been established by this construction. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoLatticeReflections
variable {V : Type*} [AddCommGroup V]
    (B : LinearMap.BilinForm ℤ V)

 def Roots := {x : V // B x x=2}
 def reflection (a x : V) : V := x-B x a • a

 theorem pairing_reflection (a x : V) (ha : B a a=2) :
    B (reflection B a x) a= -(B x a) := by
  simp only [reflection,map_sub,LinearMap.sub_apply,B.smul_left,ha]
  ring

 theorem reflection_involutive (a : V) (ha : B a a=2) :
    Function.Involutive (reflection B a) := by
  intro x
  unfold reflection
  have hp : B (x-B x a • a) a= -(B x a) := pairing_reflection B a x ha
  rw [hp,neg_smul]
  abel

 theorem norm_reflection (hs : ∀ x y,B x y=B y x) (a x : V) (ha : B a a=2) :
    B (reflection B a x) (reflection B a x)=B x x := by
  simp only [reflection,map_sub,LinearMap.sub_apply,B.smul_left,B.smul_right]
  rw [hs a x,ha]
  ring

 def reflectionPerm (hs : ∀ x y,B x y=B y x) (a : Roots B) : Roots B≃Roots B where
  toFun x := ⟨reflection B a.val x.val,(norm_reflection B hs a.val x.val a.property).trans x.property⟩
  invFun x := ⟨reflection B a.val x.val,(norm_reflection B hs a.val x.val a.property).trans x.property⟩
  left_inv x := Subtype.ext (reflection_involutive B a.val a.property x.val)
  right_inv x := Subtype.ext (reflection_involutive B a.val a.property x.val)

@[simp] theorem reflectionPerm_val (hs : ∀ x y,B x y=B y x) (a x : Roots B) :
    (reflectionPerm B hs a x).val=x.val-B x.val a.val • a.val := rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoLatticeReflections
