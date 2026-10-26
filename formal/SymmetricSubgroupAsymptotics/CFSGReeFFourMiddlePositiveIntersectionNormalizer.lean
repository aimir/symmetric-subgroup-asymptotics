import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveKernelIntersection
import SymmetricSubgroupAsymptotics.CyclicFourInvolutionIntersection

/-! An actual positive intersection is normalized by the positive group
and the actual middle Weyl involution. This follows from the SAME
normal strict kernel and its proved positive recognition, not from
recognition of a Levi group or an assertion of full-kernel containment. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveIntersectionNormalizer
open CFSGReeFFourMiddlePositiveKernelIntersection CFSGReeFFourMiddleGradedKernel
open CFSGReeFFourMiddleParabolicFlag CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourMiddleDerivedFiveWord CFSGGradedMatrixSubgroups

def middlePositiveIntersection (m : ℕ) : Subgroup (originalModelFixed m) :=
  fixedPositive m⊓(fixedPositive m).comap (MulAut.conj (middleFixedWeyl m)).toMonoidHom

theorem positive_le_normalizer_middle_intersection (m : ℕ) :
    fixedPositive m≤Subgroup.normalizer
      (middlePositiveIntersection m : Set (originalModelFixed m)) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro u hu p hp
  have hp0 : p∈fixedPositive m := hp.1
  have hpos : u*p*u⁻¹∈fixedPositive m :=
    (fixedPositive m).mul_mem ((fixedPositive m).mul_mem hu hp0)
      ((fixedPositive m).inv_mem hu)
  let A : middleParabolic m := ⟨u,positive_le_parabolic m hu⟩
  let B : middleParabolic m := ⟨p,positive_le_parabolic m hp0⟩
  have hK : B∈gradedKernel m :=
    (positive_strict_iff_opposite_positive m p hp0).mpr hp.2
  have hc := (gradedKernel_normal m).conj_mem B hK A
  have hs : fixedRawHom m (u*p*u⁻¹)∈strictUnits middleWeight := hc
  exact ⟨hpos,(positive_strict_iff_opposite_positive m (u*p*u⁻¹) hpos).mp hs⟩

theorem middle_weyl_normalizes_intersection (m : ℕ) :
    middleFixedWeyl m∈Subgroup.normalizer
      (middlePositiveIntersection m : Set (originalModelFixed m)) :=
  CyclicFourInvolutionIntersection.normalizes_intersection
    (fixedPositive m) (middleFixedWeyl m) (middleWeyl_square m)

theorem positive_weyl_join_normalizes_intersection (m : ℕ) :
    fixedPositive m⊔Subgroup.zpowers (middleFixedWeyl m)≤Subgroup.normalizer
      (middlePositiveIntersection m : Set (originalModelFixed m)) :=
  sup_le (positive_le_normalizer_middle_intersection m)
    (Subgroup.zpowers_le.mpr (middle_weyl_normalizes_intersection m))

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveIntersectionNormalizer
