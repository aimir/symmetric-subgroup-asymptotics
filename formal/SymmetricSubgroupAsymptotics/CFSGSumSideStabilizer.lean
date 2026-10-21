import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Sum.Basic

/-! Restrict an actual permutation preserving the two sides of a sum to
its original point and dual-point types. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSumSideStabilizer
variable {P H : Type*}

def side : P⊕H→Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

def sideStabilizer : Subgroup (Equiv.Perm (P⊕H)) where
  carrier := {a | ∀x,side (a x)=side x}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb x
    exact (ha (b x)).trans (hb x)
  inv_mem' := by
    intro a ha x
    simpa only [Equiv.apply_symm_apply] using (ha (a.symm x)).symm

theorem exists_left (a : sideStabilizer (P:=P) (H:=H)) (p : P) :
    ∃q : P,a.val (Sum.inl p)=Sum.inl q := by
  have hh := (show ∀x,side (a.val x)=side x from a.property) (Sum.inl p)
  cases he : a.val (Sum.inl p) with
  | inl q => exact ⟨q,rfl⟩
  | inr h =>
    simp only [he,side] at hh
    cases hh

theorem exists_right (a : sideStabilizer (P:=P) (H:=H)) (h : H) :
    ∃k : H,a.val (Sum.inr h)=Sum.inr k := by
  have hh := (show ∀x,side (a.val x)=side x from a.property) (Sum.inr h)
  cases he : a.val (Sum.inr h) with
  | inl p =>
    simp only [he,side] at hh
    cases hh
  | inr k => exact ⟨k,rfl⟩

def leftImage (a : sideStabilizer (P:=P) (H:=H)) (p : P) : P := Classical.choose (exists_left a p)
def rightImage (a : sideStabilizer (P:=P) (H:=H)) (h : H) : H := Classical.choose (exists_right a h)

theorem leftImage_spec (a : sideStabilizer (P:=P) (H:=H)) (p : P) :
    a.val (Sum.inl p)=Sum.inl (leftImage a p) := Classical.choose_spec (exists_left a p)
theorem rightImage_spec (a : sideStabilizer (P:=P) (H:=H)) (h : H) :
    a.val (Sum.inr h)=Sum.inr (rightImage a h) := Classical.choose_spec (exists_right a h)

def leftPermutation (a : sideStabilizer (P:=P) (H:=H)) : Equiv.Perm P where
  toFun := leftImage a
  invFun := leftImage a⁻¹
  left_inv p := by
    apply Sum.inl_injective (β:=H)
    rw [←leftImage_spec a⁻¹,←leftImage_spec a]
    exact a.val.symm_apply_apply _
  right_inv p := by
    apply Sum.inl_injective (β:=H)
    rw [←leftImage_spec a,←leftImage_spec a⁻¹]
    exact a.val.apply_symm_apply _

def rightPermutation (a : sideStabilizer (P:=P) (H:=H)) : Equiv.Perm H where
  toFun := rightImage a
  invFun := rightImage a⁻¹
  left_inv h := by
    apply Sum.inr_injective (α:=P)
    rw [←rightImage_spec a⁻¹,←rightImage_spec a]
    exact a.val.symm_apply_apply _
  right_inv h := by
    apply Sum.inr_injective (α:=P)
    rw [←rightImage_spec a,←rightImage_spec a⁻¹]
    exact a.val.apply_symm_apply _

def leftHom : sideStabilizer (P:=P) (H:=H)→*Equiv.Perm P where
  toFun := leftPermutation
  map_one' := by
    apply Equiv.ext
    intro p
    apply Sum.inl_injective (β:=H)
    change Sum.inl (leftImage 1 p)=Sum.inl p
    rw [←leftImage_spec]
    rfl
  map_mul' a b := by
    apply Equiv.ext
    intro p
    apply Sum.inl_injective (β:=H)
    change Sum.inl (leftImage (a*b) p)=Sum.inl (leftImage a (leftImage b p))
    rw [←leftImage_spec,←leftImage_spec,←leftImage_spec]
    rfl

def rightHom : sideStabilizer (P:=P) (H:=H)→*Equiv.Perm H where
  toFun := rightPermutation
  map_one' := by
    apply Equiv.ext
    intro h
    apply Sum.inr_injective (α:=P)
    change Sum.inr (rightImage 1 h)=Sum.inr h
    rw [←rightImage_spec]
    rfl
  map_mul' a b := by
    apply Equiv.ext
    intro h
    apply Sum.inr_injective (α:=P)
    change Sum.inr (rightImage (a*b) h)=Sum.inr (rightImage a (rightImage b h))
    rw [←rightImage_spec,←rightImage_spec,←rightImage_spec]
    rfl

end SymmetricSubgroupAsymptotics.CFSGSumSideStabilizer
