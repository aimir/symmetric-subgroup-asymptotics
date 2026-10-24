import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointTailAction
import Mathlib.GroupTheory.SemidirectProduct

/-! The checked actual tail covariance gives a literal point-radical
semidirect-product map into the SAME elementary/projective group. It
need not be injective; actual central survival is retained separately. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointExtension
open CFSGSymplecticSerreMatrices CFSGSymplecticUniformTail
open CFSGSymplecticBinaryPointTailAction
variable (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)

def tailAction (m : ℕ) : elementaryRootGroup K m →*
    MulAut (Multiplicative (CFSGSymplecticBinaryPointRadical.Coordinates K m)) where
  toFun g := {
    toFun a := Multiplicative.ofAdd (pointLinearHom K hK m g a.toAdd)
    invFun a := Multiplicative.ofAdd ((pointLinearHom K hK m g).symm a.toAdd)
    left_inv a := (pointLinearHom K hK m g).symm_apply_apply a.toAdd
    right_inv a := (pointLinearHom K hK m g).apply_symm_apply a.toAdd
    map_mul' a b := (pointLinearHom K hK m g).map_add a.toAdd b.toAdd }
  map_one' := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    change pointLinearHom K hK m 1 a.toAdd = a.toAdd
    rw [map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    change pointLinearHom K hK m (g*h) a.toAdd =
      pointLinearHom K hK m g (pointLinearHom K hK m h a.toAdd)
    rw [map_mul]
    rfl

theorem tailAction_apply (m : ℕ) (g : elementaryRootGroup K m)
    (a : Multiplicative (CFSGSymplecticBinaryPointRadical.Coordinates K m)) :
    tailAction K hK m g a = Multiplicative.ofAdd (pointLinearHom K hK m g a.toAdd) := rfl

abbrev PointParabolic (m : ℕ) :=
  Multiplicative (CFSGSymplecticBinaryPointRadical.Coordinates K m) ⋊[tailAction K hK m]
    elementaryRootGroup K m

def elementaryExtensionHom (m : ℕ) (hm : 0 < m) :
    PointParabolic K hK m →* elementaryRootGroup K (m+1) :=
  SemidirectProduct.lift (CFSGSymplecticBinaryPointRadical.elementaryHom K m hm)
    (tailHom K m) (fun g => MonoidHom.ext (fun a =>
      (tail_conjugation K hK m hm g a).symm))

theorem elementaryExtensionHom_inl (m : ℕ) (hm : 0 < m)
    (a : Multiplicative (CFSGSymplecticBinaryPointRadical.Coordinates K m)) :
    elementaryExtensionHom K hK m hm (SemidirectProduct.inl a) =
      CFSGSymplecticBinaryPointRadical.elementaryHom K m hm a := by
  simp only [elementaryExtensionHom, SemidirectProduct.lift_inl]

def projectiveExtensionHom (m : ℕ) (hm : 0 < m) :
    PointParabolic K hK m →* elementaryProjective K (m+1) :=
  (binaryProjectiveEquiv K m).toMonoidHom.comp (elementaryExtensionHom K hK m hm)

theorem projectiveExtensionHom_inl (m : ℕ) (hm : 0 < m)
    (a : Multiplicative (CFSGSymplecticBinaryPointRadical.Coordinates K m)) :
    projectiveExtensionHom K hK m hm (SemidirectProduct.inl a) =
      CFSGSymplecticBinaryPointRadical.projectiveHom K m hm a := by
  change binaryProjectiveEquiv K m (elementaryExtensionHom K hK m hm (SemidirectProduct.inl a)) = _
  rw [elementaryExtensionHom_inl]
  rfl

theorem projectiveExtensionHom_central_ne_one (m : ℕ) (hm : 0 < m) :
    projectiveExtensionHom K hK m hm
      (SemidirectProduct.inl (Multiplicative.ofAdd (0,(1 : K)))) ≠ 1 := by
  rw [projectiveExtensionHom_inl]
  exact CFSGSymplecticBinaryPointRadical.projective_central_ne_one K m hm 1 one_ne_zero

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointExtension
