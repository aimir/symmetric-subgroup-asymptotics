import SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingCentre
import Mathlib.Algebra.Module.ZMod

/-! Actual group automorphisms restrict to the characteristic centre.
Scalar-centre coordinates then give only a prime-field linear action;
no full-field linearity or scalar character is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarCentrePrimeFieldAction
open CentralExtensionScalarPairingIndex CentralExtensionScalarPairingCentre
variable {N : Type*} [Group N]

def centreAction : MulAut N →* MulAut (Subgroup.center N) where
  toFun := Subgroup.centerCongr
  map_one' := by apply MulEquiv.ext; intro x; apply Subtype.ext; rfl
  map_mul' f g := by apply MulEquiv.ext; intro x; apply Subtype.ext; rfl

theorem centreAction_val (f : MulAut N) (x : Subgroup.center N) :
    (centreAction f x).val = f x.val := rfl

variable {K : Type*} [Field K]

private def additiveAut (f : MulAut (Multiplicative K)) : AddAut K where
  toFun x := (f (Multiplicative.ofAdd x)).toAdd
  invFun x := (f.symm (Multiplicative.ofAdd x)).toAdd
  left_inv x := f.symm_apply_apply (Multiplicative.ofAdd x)
  right_inv x := f.apply_symm_apply (Multiplicative.ofAdd x)
  map_add' x y := map_mul f (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)

def linearAut (p : ℕ) [Module (ZMod p) K] (f : MulAut (Multiplicative K)) :
    K ≃ₗ[ZMod p] K :=
  { additiveAut f with map_smul' := ZMod.map_smul (additiveAut f) }

def linearAction (p : ℕ) [Module (ZMod p) K] :
    MulAut (Multiplicative K) →* K ≃ₗ[ZMod p] K where
  toFun := linearAut p
  map_one' := by apply LinearEquiv.ext; intro x; rfl
  map_mul' f g := by apply LinearEquiv.ext; intro x; rfl

variable {V : Type*} [AddCommGroup V] [Module K V]

def scalarCentreAction (D : Data (F := K) (V := V) (N := N)) :
    MulAut N →* MulAut (Multiplicative K) :=
  (MulAut.congr (centralEquiv D).symm).toMonoidHom.comp centreAction

theorem scalarCentreAction_apply (D : Data (F := K) (V := V) (N := N))
    (f : MulAut N) (a : Multiplicative K) :
    D.central (scalarCentreAction D f a) = f (D.central a) := by
  have h := (centralEquiv D).apply_symm_apply
    (centreAction f (centralEquiv D a))
  exact congrArg Subtype.val h

end SymmetricSubgroupAsymptotics.ScalarCentrePrimeFieldAction
