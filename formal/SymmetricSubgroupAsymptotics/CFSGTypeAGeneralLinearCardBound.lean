import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.GroupTheory.Index

/-! Cardinal inequalities from actual determinant and central quotients.
No order formula for SL or PSL is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeAGeneralLinearCardBound
open Matrix
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

abbrev SL := Matrix.SpecialLinearGroup n F
abbrev PSL := Matrix.ProjectiveSpecialLinearGroup n F

def determinantKernelEquiv :
    (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup n F→*Fˣ).ker≃SL (F:=F) (n:=n) where
  toFun A := ⟨A.val.val,by
    have hdet : Matrix.GeneralLinearGroup.det A.val=1 := A.property
    exact congrArg (fun z : Fˣ => (z : F)) hdet⟩
  invFun A := ⟨Matrix.SpecialLinearGroup.toGL A,Matrix.SpecialLinearGroup.coeToGL_det A⟩
  left_inv A := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    rfl

theorem generalLinear_card_le_specialLinear_mul_units [Finite F] :
    Nat.card (Matrix.GeneralLinearGroup n F)≤Nat.card (SL (F:=F) (n:=n))*Nat.card Fˣ := by
  let f : Matrix.GeneralLinearGroup n F→*Fˣ := Matrix.GeneralLinearGroup.det
  have hker : Nat.card f.ker=Nat.card (SL (F:=F) (n:=n)) :=
    Nat.card_congr determinantKernelEquiv
  have hi : f.ker.index≤Nat.card Fˣ := by
    rw [Subgroup.index_ker]
    exact Nat.card_le_card_of_injective (fun z : f.range => (z : Fˣ)) Subtype.val_injective
  calc
    Nat.card (Matrix.GeneralLinearGroup n F)=Nat.card f.ker*f.ker.index := f.ker.card_mul_index.symm
    _≤Nat.card f.ker*Nat.card Fˣ := Nat.mul_le_mul_left _ hi
    _=Nat.card (SL (F:=F) (n:=n))*Nat.card Fˣ := congrArg (fun k : ℕ => k*Nat.card Fˣ) hker

theorem specialLinear_center_card_le_units [Finite F] :
    Nat.card (Subgroup.center (SL (F:=F) (n:=n)))≤Nat.card Fˣ := by
  let e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n:=n) (R:=F)
  exact Nat.card_le_card_of_injective (fun z : Subgroup.center (SL (F:=F) (n:=n)) =>
    ((e z) : Fˣ)) (Subtype.val_injective.comp e.injective)

theorem specialLinear_card_le_projective_mul_units [Finite F] :
    Nat.card (SL (F:=F) (n:=n))≤Nat.card (PSL (F:=F) (n:=n))*Nat.card Fˣ := by
  have hc := (Subgroup.center (SL (F:=F) (n:=n))).card_mul_index
  have hi : (Subgroup.center (SL (F:=F) (n:=n))).index=
      Nat.card (PSL (F:=F) (n:=n)) := rfl
  rw [hi] at hc
  calc
    Nat.card (SL (F:=F) (n:=n))=
        Nat.card (Subgroup.center (SL (F:=F) (n:=n)))*Nat.card (PSL (F:=F) (n:=n)) := hc.symm
    _≤Nat.card Fˣ*Nat.card (PSL (F:=F) (n:=n)) :=
      Nat.mul_le_mul_right _ specialLinear_center_card_le_units
    _=Nat.card (PSL (F:=F) (n:=n))*Nat.card Fˣ := Nat.mul_comm _ _

theorem generalLinear_card_le_units_sq_mul_projective [Finite F] :
    Nat.card (Matrix.GeneralLinearGroup n F)≤Nat.card Fˣ^2*Nat.card (PSL (F:=F) (n:=n)) := by
  calc
    Nat.card (Matrix.GeneralLinearGroup n F)≤Nat.card (SL (F:=F) (n:=n))*Nat.card Fˣ :=
      generalLinear_card_le_specialLinear_mul_units
    _≤(Nat.card (PSL (F:=F) (n:=n))*Nat.card Fˣ)*Nat.card Fˣ :=
      Nat.mul_le_mul_right _ specialLinear_card_le_projective_mul_units
    _=Nat.card (PSL (F:=F) (n:=n))*(Nat.card Fˣ*Nat.card Fˣ) := Nat.mul_assoc _ _ _
    _=(Nat.card Fˣ*Nat.card Fˣ)*Nat.card (PSL (F:=F) (n:=n)) := Nat.mul_comm _ _
    _=Nat.card Fˣ^2*Nat.card (PSL (F:=F) (n:=n)) := by rw [pow_two]

end SymmetricSubgroupAsymptotics.CFSGTypeAGeneralLinearCardBound
