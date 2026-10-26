import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicOuterBlocks
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTailThirdRemainder

/-! The retained height-three correction is a point of the SAME
intrinsic radical R, via the proved full-centre quotient restriction.
No inclusion in the Frattini subgroup or characteristic kernel is
inferred from its vanishing first two matrix layers. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicThirdCorrection
open CFSGTitsIntrinsicOuterBlocks CFSGTitsIntrinsicFirstLayer CFSGTitsIntrinsicMiddleRadical
open CFSGReeFFourMiddleTailThirdRemainder CFSGReeFFourInnerBracketOriginalBlocks
open CFSGReeFFourBinaryOuterSaving CFSGReeFFourMiddlePositiveIntersectionNormalizer
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGReeFFourOuterThreeWord CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourMiddleGradedKernel
open CFSGTwistedE6GeckDiagramCovariance
private abbrev D := commutator (originalModelFixed 0)

private theorem conjugate_mem_reverse {G : Type*} [Group G]
    (P : Subgroup G) (w x : G)
    (hw : w∈Subgroup.normalizer (P : Set G))
    (hx : (MulAut.conj w) x∈P) : x∈P :=
  (Subgroup.mem_normalizer_iff.mp hw x).mpr hx

private theorem first_block_value (m : ℕ) :
    actualOuterBlock m 0=(MulAut.conj (middleFixedWeyl m)) (outerInvolution m) := rfl

private theorem outer_intersection (m : ℕ) :
    outerInvolution m∈middlePositiveIntersection m := by
  have hc : (MulAut.conj (middleFixedWeyl m)) (outerInvolution m)∈
      middlePositiveIntersection m :=
    Eq.mp (congrArg (fun x => x∈middlePositiveIntersection m) (first_block_value m))
      (actualBlock_intersection m 0)
  exact conjugate_mem_reverse (middlePositiveIntersection m) _ _
    (middle_weyl_normalizes_intersection m) hc

private theorem word_membership {G : Type*} [Group G] (P : Subgroup G)
    (x c d e : G) (hx : x∈P) (hc : c∈P) (hd : d∈P) (he : e∈P) :
    (x*c*x⁻¹*c⁻¹)*(d*e)⁻¹∈P :=
  P.mul_mem (P.mul_mem (P.mul_mem (P.mul_mem hx hc) (P.inv_mem hx)) (P.inv_mem hc))
    (P.inv_mem (P.mul_mem hd he))

theorem correctionWord_derived (m : ℕ) :
    correctionWord m∈commutator (originalModelFixed m) :=
  word_membership (commutator (originalModelFixed m)) _ _ _ _
    (outer_mem_derived m) (actualBlock_derived m 0)
    (actualBlock_derived m 1) (actualBlock_derived m 2)

theorem correctionWord_intersection (m : ℕ) :
    correctionWord m∈middlePositiveIntersection m :=
  word_membership (middlePositiveIntersection m) _ _ _ _
    (outer_intersection m) (actualBlock_intersection m 0)
    (actualBlock_intersection m 1) (actualBlock_intersection m 2)

def correctionSource : sourceIntersection :=
  ⟨⟨correctionWord 0,correctionWord_derived 0⟩,correctionWord_intersection 0⟩

def correctionPoint : middleRadical := sourceEquiv correctionSource

private theorem comp_equiv_inverse {G H C : Type*} [Group G] [Group H] [Group C]
    (f : G→*C) (e : G≃*H) (x : G) :
    (f.comp e.symm.toMonoidHom) (e x)=f x := by
  change f (e.symm (e x))=f x
  rw [e.symm_apply_apply]

theorem correctionPoint_raw :
    radicalRawHom correctionPoint=fixedRawHom 0 (correctionWord 0) :=
  comp_equiv_inverse ((fixedRawHom 0).comp (D.subtype.comp sourceIntersection.subtype))
    sourceEquiv correctionSource

theorem correctionPoint_height_three :
    ∀i j,middleWeight i≤middleWeight j+2→
      (radicalRawHom correctionPoint : Matrix GeckIndex GeckIndex (Field 0)) i j=
        (1 : Matrix GeckIndex GeckIndex (Field 0)) i j := by
  intro i j hij
  exact (congrArg (fun u : (Matrix GeckIndex GeckIndex (Field 0))ˣ=>
    (u : Matrix GeckIndex GeckIndex (Field 0)) i j) correctionPoint_raw).trans
      (correctionWord_height_three 0 i j hij)

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicThirdCorrection
