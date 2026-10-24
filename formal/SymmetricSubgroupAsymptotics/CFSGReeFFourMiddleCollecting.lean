import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleParameterHoms
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleCentrality

/-! Bounded middle B2 collection in the literal original Ree defining
field. The two higher factors are central relative to the middle axes;
their involutions follow from additive parameters in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleCollecting
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalMiddleLongCentrality
open CFSGFFourOriginalMiddleParameterHoms CFSGReeFFourMiddleCentrality
open CFSGReeFFourFieldParameters
local notation "A" => CartanMatrix.F₄

theorem middleLong_inv (m : ℕ) (r : Field m) :
    (middleLong (Field m) r)⁻¹=middleLong (Field m) r := by
  have h := map_inv (middleLongHom (Field m)) (Multiplicative.ofAdd r)
  change middleLong (Field m) (-r)=(middleLong (Field m) r)⁻¹ at h
  rw [CharTwo.neg_eq] at h
  exact h.symm

theorem middleShort_inv (m : ℕ) (r : Field m) :
    (middleShort (Field m) r)⁻¹=middleShort (Field m) r := by
  have h := map_inv (middleShortHom (Field m)) (Multiplicative.ofAdd r)
  change middleShort (Field m) (-r)=(middleShort (Field m) r)⁻¹ at h
  rw [CharTwo.neg_eq] at h
  exact h.symm

theorem middle_reverse_axes (m : ℕ) (a b : Field m) :
    modelRoot A (Field m) false 2 b*modelRoot A (Field m) false 1 a=
      (middleLong (Field m) (a^2*b)*middleShort (Field m) (a*b))*
        modelRoot A (Field m) false 1 a*modelRoot A (Field m) false 2 b := by
  have hi : (middleLong (Field m) (a^2*b)*middleShort (Field m) (a*b))⁻¹=
      middleLong (Field m) (a^2*b)*middleShort (Field m) (a*b) := by
    rw [mul_inv_rev,middleShort_inv,middleLong_inv]
    exact (middleLong_commute_middleShort m (a^2*b) (a*b)).eq.symm
  calc
    _=(middleLong (Field m) (a^2*b)*middleShort (Field m) (a*b))⁻¹*
        modelRoot A (Field m) false 1 a*modelRoot A (Field m) false 2 b := by
      rw [←middle_commutator]
      simp only [commutatorElement_def]
      group
    _=_ := by rw [hi]

theorem middle_collect_central (m : ℕ) (a b r s u v : Field m) :
    (middleLong (Field m) r*middleShort (Field m) s)*
      (modelRoot A (Field m) false 1 a*modelRoot A (Field m) false 2 b)*
      (middleShort (Field m) u*middleLong (Field m) v)=
    modelRoot A (Field m) false 1 a*modelRoot A (Field m) false 2 b*
      middleLong (Field m) (r+v)*middleShort (Field m) (s+u) := by
  have hx := (middleLong_commute_one (Field m) r a).mul_left (middleShort_commute_one m s a)
  have hy := (middleLong_commute_two (Field m) r b).mul_left (middleShort_commute_two m s b)
  have hc := hx.mul_right hy
  have hp := ((middleLong_commute_middleShort m v s).mul_right
    (middleLong_commute_middleShort m v u)).symm
  rw [hc.eq]
  calc
    _=(modelRoot A (Field m) false 1 a*modelRoot A (Field m) false 2 b)*
      (middleLong (Field m) r*((middleShort (Field m) s*middleShort (Field m) u)*
        middleLong (Field m) v)) := by group
    _=(modelRoot A (Field m) false 1 a*modelRoot A (Field m) false 2 b)*
      (middleLong (Field m) r*(middleLong (Field m) v*
        (middleShort (Field m) s*middleShort (Field m) u))) := by rw [hp.eq]
    _=modelRoot A (Field m) false 1 a*modelRoot A (Field m) false 2 b*
      (middleLong (Field m) r*middleLong (Field m) v)*
      (middleShort (Field m) s*middleShort (Field m) u) := by group
    _=_ := by rw [←middleLong_add,←middleShort_add]

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleCollecting
