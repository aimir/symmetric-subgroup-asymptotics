import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleRadical
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupFirstLayer
import Mathlib.GroupTheory.Abelianization.Defs

/-! Actual first-layer coordinates on the SAME intrinsic Tits 2-layer.
The faithful source equivalence is only the proved restriction of the
FULL central quotient. Commutators and squares lie in the kernel; the
reverse kernel inclusion, characteristicity and any dimension remain
separate obligations. No target automorphism is made matrix-linear. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFirstLayer
open CFSGTitsIntrinsicMiddleRadical CFSGTitsAmbientPairAlignment
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourAllParameterDerivedPositive
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourMiddleGradedKernel
open CFSGReeFFourMiddlePositiveKernelIntersection CFSGGradedMatrixSubgroups
open CFSGReeFFourMiddlePositiveIntersectionNormalizer CFSGReeFFourFieldParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGGradedMatrixGroupFirstLayer
private abbrev D := commutator (originalModelFixed 0)

def sourceHom : sourceIntersection →* CFSG.Models.Tits :=
  (derivedReeHom 0).comp sourceIntersection.subtype

theorem sourceHom_injective : Function.Injective sourceHom := by
  intro x y h
  have hx : x.val∈derivedPositive 0 := x.property.1
  have hy : y.val∈derivedPositive 0 := y.property.1
  have he : (⟨x.val,hx⟩ : derivedPositive 0)=(⟨y.val,hy⟩ : derivedPositive 0) :=
    titsPositiveHom_injective h
  exact Subtype.ext (congrArg (fun z : derivedPositive 0 => (z : D)) he)

private theorem sourceHom_range : sourceHom.range=middleRadical := by
  have he : sourceHom.range=sourceIntersection.map (derivedReeHom 0) := by
    rw [sourceHom,MonoidHom.range_comp,sourceIntersection.range_subtype]
  exact he.trans sourceIntersection_image

def sourceEquiv : sourceIntersection≃*middleRadical :=
  (MonoidHom.ofInjective sourceHom_injective).trans (MulEquiv.subgroupCongr sourceHom_range)

private def sourceRawHom :=
  (fixedRawHom 0).comp (D.subtype.comp sourceIntersection.subtype)

def radicalRawHom := sourceRawHom.comp sourceEquiv.symm.toMonoidHom

theorem radicalRawHom_strict (x : middleRadical) : radicalRawHom x∈strictUnits middleWeight := by
  let z : sourceIntersection := sourceEquiv.symm x
  have hp : (z.val : originalModelFixed 0)∈fixedPositive 0 := z.property.1
  have hc : CFSGReeFFourRelativePositiveSubgroups.middleFixedWeyl 0*
      (z.val : originalModelFixed 0)*
      (CFSGReeFFourRelativePositiveSubgroups.middleFixedWeyl 0)⁻¹∈fixedPositive 0 := z.property.2
  change fixedRawHom 0 (z.val : originalModelFixed 0)∈strictUnits middleWeight
  exact (positive_strict_iff_opposite_positive 0 (z.val : originalModelFixed 0) hp).mpr hc

def firstLayerHom : middleRadical →* Multiplicative (Matrix GeckIndex GeckIndex (Field 0)) where
  toFun x := Multiplicative.ofAdd (firstLayer middleWeight (radicalRawHom x))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change firstLayer middleWeight (radicalRawHom 1)=0
    rw [map_one,firstLayer_one]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change firstLayer middleWeight (radicalRawHom (x*y))=
      firstLayer middleWeight (radicalRawHom x)+firstLayer middleWeight (radicalRawHom y)
    rw [map_mul]
    exact firstLayer_mul middleWeight (radicalRawHom x) (radicalRawHom y)
      (radicalRawHom_strict x) (radicalRawHom_strict y)

theorem firstLayerHom_value (x : middleRadical) :
    (firstLayerHom x).toAdd=firstLayer middleWeight (radicalRawHom x) := rfl

theorem commutator_le_firstLayer_kernel : commutator middleRadical≤firstLayerHom.ker :=
  Abelianization.commutator_subset_ker firstLayerHom

theorem square_mem_firstLayer_kernel (x : middleRadical) : x^2∈firstLayerHom.ker := by
  change firstLayerHom (x^2)=1
  apply Multiplicative.toAdd.injective
  rw [map_pow,pow_two]
  change (firstLayerHom x).toAdd+(firstLayerHom x).toAdd=0
  ext i j
  exact CharTwo.add_self_eq_zero _

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFirstLayer
