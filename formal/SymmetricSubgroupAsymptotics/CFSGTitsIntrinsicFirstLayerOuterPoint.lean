import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFirstLayer
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterFirstLayerEntry
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving

/-! A nonzero point in the first-layer image of the SAME intrinsic
radical R. The literal original outer parameter is first placed in the
actual derived/strict intersection, then transported by the proved
full-centre-quotient restriction. No head dimension or characteristic
kernel assertion follows from this one point. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFirstLayerOuterPoint
open CFSGTitsIntrinsicFirstLayer CFSGTitsIntrinsicMiddleRadical
open CFSGReeFFourOuterFirstLayerEntry CFSGReeFFourBinaryOuterSaving
open CFSGReeFFourMiddlePositiveKernelIntersection
open CFSGReeFFourMiddlePositiveIntersectionNormalizer CFSGReeFFourMiddleGradedKernel
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourOuterFixedRoot CFSGReeFFourOuterThreeWord
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourFieldParameters
open CFSGFFourOriginalMiddleWords CFSGGradedMatrixSubgroups
private abbrev D := commutator (originalModelFixed 0)

private theorem fixed_outer_raw (m : ℕ) (a : Field m) :
    fixedRawHom m (fixedOuterHom m (Multiplicative.ofAdd a))=
      rawHom (Field m) (outerWord m a) := rfl

private theorem comap_membership {G H : Type*} [Group G] [Group H]
    (f : G →* H) (K : Subgroup H) (x : G) (hx : x∈K.comap f) : f x∈K := hx

private theorem comp_subtype_apply {G H : Type*} [Group G] [Group H]
    (f : G →* H) (P : Subgroup G) (x : P) : f.comp P.subtype x=f x.val := rfl

private theorem outer_parabolic_value (m : ℕ) :
    (outerParameter m 1).val=outerInvolution m := rfl

private theorem raw_parabolic_apply (m : ℕ)
    (x : CFSGReeFFourMiddleParabolicFlag.middleParabolic m) :
    parabolicRawHom m x=fixedRawHom m x.val :=
  comp_subtype_apply (fixedRawHom m) _ x

private theorem raw_outer_parabolic (m : ℕ) :
    parabolicRawHom m (outerParameter m 1)=fixedRawHom m (outerInvolution m) :=
  (raw_parabolic_apply m (outerParameter m 1)).trans
    (congrArg (fixedRawHom m) (outer_parabolic_value m))

private theorem outer_strict (m : ℕ) :
    fixedRawHom m (outerInvolution m)∈strictUnits middleWeight := by
  have hs := comap_membership (parabolicRawHom m)
    (strictUnits (K := Field m) middleWeight) (outerParameter m 1)
    (outerParameter_mem_gradedKernel m 1)
  exact Eq.mp (congrArg (fun z => z∈strictUnits (K := Field m) middleWeight)
    (raw_outer_parabolic m)) hs

private theorem mem_intersection {G : Type*} [Group G]
    (U : Subgroup G) (w x : G) (hx : x∈U) (hc : w*x*w⁻¹∈U) :
    x∈U⊓U.comap (MulAut.conj w).toMonoidHom := ⟨hx,hc⟩

private theorem outer_intersection (m : ℕ) :
    outerInvolution m∈middlePositiveIntersection m :=
  mem_intersection (fixedPositive m) (middleFixedWeyl m) (outerInvolution m)
    (fixedOuterHom_range_le_fixedPositive m ⟨Multiplicative.ofAdd 1,rfl⟩)
    ((positive_strict_iff_opposite_positive m (outerInvolution m)
      (fixedOuterHom_range_le_fixedPositive m ⟨Multiplicative.ofAdd 1,rfl⟩)).mp
        (outer_strict m))

private def sourcePoint : sourceIntersection :=
  ⟨⟨outerInvolution 0,outer_mem_derived 0⟩,outer_intersection 0⟩

def outerPoint : middleRadical := sourceEquiv sourcePoint

private theorem comp_equiv_inverse {G H C : Type*} [Group G] [Group H] [Group C]
    (f : G →* C) (e : G≃*H) (x : G) : (f.comp e.symm.toMonoidHom) (e x)=f x := by
  change f (e.symm (e x))=f x
  rw [e.symm_apply_apply]

private theorem raw_sourceEquiv (z : sourceIntersection) :
    radicalRawHom (sourceEquiv z)=fixedRawHom 0 (z.val : originalModelFixed 0) :=
  comp_equiv_inverse ((fixedRawHom 0).comp (D.subtype.comp sourceIntersection.subtype))
    sourceEquiv z

private theorem outerPoint_raw :
    radicalRawHom outerPoint=rawHom (Field 0) (outerWord 0 1) :=
  (raw_sourceEquiv sourcePoint).trans (fixed_outer_raw 0 1)

theorem outerPoint_firstLayer_ne_zero : firstLayerHom outerPoint≠1 := by
  intro h
  have hh := congrArg (fun x => x.toAdd) h
  change CFSGGradedMatrixGroupFirstLayer.firstLayer middleWeight
    (radicalRawHom outerPoint)=0 at hh
  rw [outerPoint_raw] at hh
  exact outer_firstLayer_ne_zero 0 1 one_ne_zero hh

theorem firstLayer_kernel_ne_top : firstLayerHom.ker≠⊤ := by
  intro h
  have hx : outerPoint∈firstLayerHom.ker := by rw [h]; trivial
  exact outerPoint_firstLayer_ne_zero hx

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFirstLayerOuterPoint
