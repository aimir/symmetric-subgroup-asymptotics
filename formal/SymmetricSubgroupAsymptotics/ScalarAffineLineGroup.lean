import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Units
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-! Literal scalar affine-line coordinates. The additive translation
kernel, multiplicative scalar quotient and their actual conjugation
formula are proved inside the same semidirect product, over any field.
These coordinates will be specialized to a prime field at the ordinary
normal-generation boundary. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ScalarAffineLineGroup

variable (k : Type) [Field k]

def scalarAction : kˣ →* MulAut (Multiplicative k) where
  toFun u := (u.mulLeftLinearEquiv k k).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro z
    apply Multiplicative.toAdd.injective
    change (↑(1:kˣ):k) * z.toAdd = z.toAdd
    rw [Units.val_one,one_mul]
  map_mul' u v := by
    apply MulEquiv.ext
    intro z
    apply Multiplicative.toAdd.injective
    change (↑(u*v):k) * z.toAdd = (u:k) * ((v:k) * z.toAdd)
    rw [Units.val_mul,mul_assoc]

abbrev Line := Multiplicative k ⋊[scalarAction k] kˣ

instance [Finite k] : Finite (Line k) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

abbrev scalar : Line k →* kˣ := SemidirectProduct.rightHom
abbrev translation : Multiplicative k →* Line k := SemidirectProduct.inl

def pointAction : Line k →* Equiv.Perm k where
  toFun g := {
    toFun x := g.left.toAdd + (g.right:k) * x
    invFun x := (↑(g.right⁻¹):k) * (x-g.left.toAdd)
    left_inv x := by simp
    right_inv x := by simp [mul_sub] }
  map_one' := by
    apply Equiv.ext
    intro x
    change 0 + (↑(1:kˣ):k)*x = x
    rw [Units.val_one,one_mul,zero_add]
  map_mul' g h := by
    apply Equiv.ext
    intro x
    change (g.left.toAdd + (g.right:k)*h.left.toAdd) +
      (↑(g.right*h.right):k)*x =
        g.left.toAdd + (g.right:k)*(h.left.toAdd+(h.right:k)*x)
    rw [Units.val_mul]
    ring

theorem pointAction_apply (g : Line k) (x : k) :
    pointAction k g x = g.left.toAdd + (g.right:k)*x := rfl

theorem pointAction_injective : Function.Injective (pointAction k) := by
  intro g h he
  have hzero := Equiv.congr_fun he (0:k)
  have hleft : g.left = h.left := Multiplicative.toAdd.injective
    (by simpa only [pointAction_apply,mul_zero,add_zero] using hzero)
  have hone := Equiv.congr_fun he (1:k)
  have hright : g.right = h.right := by
    apply Units.ext
    have hh : g.left.toAdd+(g.right:k) = g.left.toAdd+(h.right:k) := by
      simpa only [pointAction_apply,mul_one,hleft] using hone
    exact add_left_cancel hh
  exact SemidirectProduct.ext hleft hright

/-- The actual scalar-projection kernel is exactly the additive line. -/
def translationKernelEquiv : (scalar k).ker ≃* Multiplicative k where
  toFun u := u.val.left
  invFun z := ⟨translation k z,rfl⟩
  left_inv u := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact u.property.symm
  right_inv _ := rfl
  map_mul' u v := by
    change u.val.left * scalarAction k u.val.right v.val.left = u.val.left*v.val.left
    have hu : u.val.right = 1 := u.property
    rw [hu,map_one]
    rfl

theorem translationKernelEquiv_translation (z : Multiplicative k) :
    translationKernelEquiv k ⟨translation k z,rfl⟩ = z := rfl

theorem translation_kernelCoordinate (u : (scalar k).ker) :
    translation k (translationKernelEquiv k u) = u.val := by
  apply SemidirectProduct.ext
  · rfl
  · exact u.property.symm

/-- Conjugation by the whole affine group, including its translation
part, acts on translations through the literal scalar projection. -/
theorem conjugate_translation (g : Line k) (z : Multiplicative k) :
    g * translation k z * g⁻¹ = translation k (scalarAction k g.right z) := by
  rcases g with ⟨a,u⟩
  change (⟨a,u⟩ : Line k) * SemidirectProduct.inl z * (⟨a,u⟩ : Line k)⁻¹ =
    SemidirectProduct.inl (scalarAction k u z)
  rw [SemidirectProduct.mk_eq_inl_mul_inr]
  calc
    (SemidirectProduct.inl a * SemidirectProduct.inr u) * SemidirectProduct.inl z *
        (SemidirectProduct.inl a * SemidirectProduct.inr u)⁻¹ =
      SemidirectProduct.inl a *
        (SemidirectProduct.inr u * SemidirectProduct.inl z * SemidirectProduct.inr u⁻¹) *
          (SemidirectProduct.inl a)⁻¹ := by
            rw [map_inv]
            group
    _ = SemidirectProduct.inl a * SemidirectProduct.inl (scalarAction k u z) *
        (SemidirectProduct.inl a)⁻¹ := by rw [←SemidirectProduct.inl_aut]
    _ = SemidirectProduct.inl (a * scalarAction k u z * a⁻¹) := by
      rw [map_mul,map_mul,map_inv]
    _ = SemidirectProduct.inl (scalarAction k u z) := by
      congr 1
      rw [mul_comm a (scalarAction k u z),mul_assoc,mul_inv_cancel,mul_one]

theorem translationKernelEquiv_conjugation (g : Line k) (u : (scalar k).ker) :
    (translationKernelEquiv k (MulAut.conjNormal g u)).toAdd =
      (g.right:k) * (translationKernelEquiv k u).toAdd := by
  have hh := congrArg (fun v : Line k => v.left.toAdd)
    (conjugate_translation k g (translationKernelEquiv k u))
  rw [translation_kernelCoordinate] at hh
  exact hh

end SymmetricSubgroupAsymptotics.ScalarAffineLineGroup
