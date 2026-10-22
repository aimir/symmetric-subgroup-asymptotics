import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A genuine surjective coordinate homomorphism with derived kernel
transports EVERY group automorphism to its actual coordinate group.
The construction uses the original abelianization, not a chosen lift. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGDerivedCoordinateAutomorphism
variable {G C : Type*} [Group G] [CommGroup C]
    (coord : G→*C) (hsurj : Function.Surjective coord) (hker : coord.ker=commutator G)

def coordinateEquiv : Abelianization G≃*C :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective coord hsurj)

theorem coordinateEquiv_of (x : G) :
    coordinateEquiv coord hsurj hker (Abelianization.of x)=coord x := by
  change (QuotientGroup.quotientKerEquivOfSurjective coord hsurj)
    ((QuotientGroup.quotientMulEquivOfEq hker.symm) (QuotientGroup.mk x))=coord x
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

def coordinateAut (f : MulAut G) : MulAut C :=
  ((coordinateEquiv coord hsurj hker).symm.trans f.abelianizationCongr).trans
    (coordinateEquiv coord hsurj hker)

theorem coordinateAut_apply (f : MulAut G) (x : G) :
    coordinateAut coord hsurj hker f (coord x)=coord (f x) := by
  rw [←coordinateEquiv_of coord hsurj hker x]
  change coordinateEquiv coord hsurj hker
    (f.abelianizationCongr ((coordinateEquiv coord hsurj hker).symm
      (coordinateEquiv coord hsurj hker (Abelianization.of x))))=coord (f x)
  rw [MulEquiv.symm_apply_apply]
  change coordinateEquiv coord hsurj hker (Abelianization.of (f x))=coord (f x)
  exact coordinateEquiv_of coord hsurj hker (f x)

end SymmetricSubgroupAsymptotics.CFSGDerivedCoordinateAutomorphism
