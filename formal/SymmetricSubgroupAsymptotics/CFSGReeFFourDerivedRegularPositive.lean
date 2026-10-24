import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalars
import SymmetricSubgroupAsymptotics.CFSGReeFFourNontrivialTorusUnit
import SymmetricSubgroupAsymptotics.CFSGReeFFourRegularFixedPositive
import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusCommutatorLeading
import Mathlib.GroupTheory.Commutator.Basic

/-! An actual commutator in the original exceptional-fixed group has
all six ambient leading coordinates nonzero when a is not one.
The existence theorem is restricted to m>0; it says nothing about Tits. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedRegularPositive
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedTorus CFSGReeFFourFixedTorusScalars
open CFSGReeFFourNontrivialTorusUnit CFSGReeFFourRegularFixedPositive
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalProductTorus
open CFSGTwistedE6GeckPositiveTwist CFSGE6GeckProductTorus
open CFSGE6GeckProductTorusCommutatorLeading CFSGIntegerMatrixPowerHom
open CFSGFFourRelativeScalarIndex CFSGFFourE6ScalarTuple
open CFSGNormTwoCoordinateLeadingFactor CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def derivedRegular (m : ℕ) (a : (Field m)ˣ) : commutator (originalModelFixed m) :=
  ⟨⁅fixedTorus m a 1,regularFixed m⁆,
    Subgroup.commutator_mem_commutator (by trivial) (by trivial)⟩

theorem rawHom_derivedRegular (m : ℕ) (a : (Field m)ˣ) :
    rawHom (Field m) (derivedRegular m a).val.val=
      rawProductTorus (Field m) (CFSGFFourE6ProductTorus.torusTuple (Field m)
        (fixedTorusTuple m a 1))*(regularPositive m).val*
      (rawProductTorus (Field m) (CFSGFFourE6ProductTorus.torusTuple (Field m)
        (fixedTorusTuple m a 1)))⁻¹*(regularPositive m).val⁻¹ := by
  change rawHom (Field m)
    ((fixedTorus m a 1).val*(regularFixed m).val*(fixedTorus m a 1).val⁻¹*
      (regularFixed m).val⁻¹)=_
  simp only [map_mul,map_inv,fixedTorus_val,rawHom_modelProductTorus,rawHom_regularFixed]

theorem derivedRegular_positive (m : ℕ) (a : (Field m)ˣ) :
    rawHom (Field m) (derivedRegular m a).val.val∈Positive (Field m) := by
  rw [rawHom_derivedRegular]
  exact product_torus_commutator_positive (Field m)
    (CFSGFFourE6ProductTorus.torusTuple (Field m) (fixedTorusTuple m a 1)) (regularPositive m)

private theorem scalarTuple_apply (m : ℕ) (x : Fin 4→(Field m)ˣ) (i : Fin 6) :
    CFSGFFourE6ProductTorus.torusTuple (Field m) x i=x (foldedCoordinate i) := by
  fin_cases i <;> rfl

theorem derivedRegular_leading (m : ℕ) (a : (Field m)ˣ) (i : Fin 6) :
    leadingCoordinates A hd hs hp ho (Field m)
      (rawHom (Field m) (derivedRegular m a).val.val) i=
      ((powerHom relativeCartan (fixedTorusTuple m a 1) (foldedCoordinate i) : (Field m)ˣ) : Field m)-1 := by
  have hr : leadingCoordinates A hd hs hp ho (Field m) (regularPositive m).val i=1 := by
    simpa only [rawHom_regularFixed] using regularFixed_leading m i
  rw [rawHom_derivedRegular,product_torus_commutator_leading,hr,mul_one,
    CFSGFFourE6ProductTorus.powerHom_torusTuple,scalarTuple_apply]

theorem derivedRegular_leading_ne_zero (m : ℕ) (a : (Field m)ˣ) (ha : a≠1) (i : Fin 6) :
    leadingCoordinates A hd hs hp ho (Field m)
      (rawHom (Field m) (derivedRegular m a).val.val) i≠0 := by
  rw [derivedRegular_leading]
  exact sub_ne_zero.mpr (fixed_torus_scalars_ne_one m a ha (foldedCoordinate i))

theorem exists_derived_regular_positive (m : ℕ) (hm : 0<m) :
    ∃r : commutator (originalModelFixed m),
      rawHom (Field m) r.val.val∈Positive (Field m) ∧
      ∀i : Fin 6,leadingCoordinates A hd hs hp ho (Field m)
        (rawHom (Field m) r.val.val) i≠0 := by
  obtain ⟨a,ha⟩ := exists_torus_unit_ne_one m hm
  exact ⟨derivedRegular m a,derivedRegular_positive m a,derivedRegular_leading_ne_zero m a ha⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedRegularPositive
