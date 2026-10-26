import SymmetricSubgroupAsymptotics.CFSGTitsOpposedMiddleFlag
import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleSquare

/-! The negative intrinsic flag has a unique involution, the actual
opposition image of the already recovered middle square. Uniqueness
uses the original cyclic embedding transported through the actual flag
equivalences. No target automorphism is lifted to an ambient group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsOpposedMiddleSquare
open CFSGTitsOpposedMiddleFlag CFSGTitsIntrinsicMiddleFlag CFSGTitsIntrinsicMiddleSquare
open CFSGTitsAmbientPairAlignment CFSGReeFFourBinaryReflectionMiddleFlag
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourBinaryMiddleGenerators
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourMiddleSquareCommutator
open CFSGReeFFourMiddleFixedSubgroup CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourAmbientCentralQuotientAction CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourFixedAmbientHom
private abbrev D := commutator (originalModelFixed 0)
private instance fixedFinite : Finite (originalModelFixed 0) :=
  Finite.of_injective (fixedAmbientHom 0) (fixedAmbientHom_injective 0)
private def squareSource : D := ⟨(fourCycle 0)^2,square_mem_derived 0⟩

private theorem squareSource_mem_flag : squareSource∈reflectionIntersection := by
  have hm : squareSource∈(middleFixedSubgroup 0).comap D.subtype := by
    change (fourCycle 0)^2∈middleFixedSubgroup 0
    rw [middleFixed_zero_eq_zpowers]
    exact (Subgroup.zpowers (fourCycle 0)).pow_mem (Subgroup.mem_zpowers _) 2
  exact Eq.mpr (congrArg (fun U : Subgroup D => squareSource∈U)
    reflectionIntersection_eq_restricted_middle) hm

private theorem square_mem_intrinsicFlag : middleSquareRoot∈intrinsicFlag := by
  rw [←image_reflectionIntersection,middleSquareRoot_value]
  exact ⟨squareSource,squareSource_mem_flag,rfl⟩

private def positivePoint : intrinsicFlag := ⟨middleSquareRoot,square_mem_intrinsicFlag⟩
private def negativePoint : negativeIntrinsicFlag := opposedFlagEquiv positivePoint

private def originalEmbedding : reflectionIntersection →* originalModelFixed 0 :=
  D.subtype.comp reflectionIntersection.subtype
private def negativeEmbedding : negativeIntrinsicFlag →* originalModelFixed 0 :=
  originalEmbedding.comp (flagEquiv.symm.toMonoidHom.comp opposedFlagEquiv.symm.toMonoidHom)

private theorem negativeEmbedding_injective : Function.Injective negativeEmbedding := by
  intro x y h
  apply opposedFlagEquiv.symm.injective
  apply flagEquiv.symm.injective
  exact Subtype.ext (Subtype.ext h)

private theorem negativeEmbedding_mem_cyclic (x : negativeIntrinsicFlag) :
    negativeEmbedding x∈Subgroup.zpowers (fourCycle 0) := by
  let z : reflectionIntersection := flagEquiv.symm (opposedFlagEquiv.symm x)
  have hm : z.val∈(middleFixedSubgroup 0).comap D.subtype :=
    Eq.mp (congrArg (fun U : Subgroup D => z.val∈U)
      reflectionIntersection_eq_restricted_middle) z.property
  change (z.val : originalModelFixed 0)∈Subgroup.zpowers (fourCycle 0)
  rw [←middleFixed_zero_eq_zpowers]
  exact hm

private theorem negativePoint_square : negativePoint^2=1 := by
  have hp : positivePoint^2=1 := Subtype.ext middleSquareRoot_square
  exact (map_pow opposedFlagEquiv positivePoint 2).symm.trans
    ((congrArg opposedFlagEquiv hp).trans (map_one opposedFlagEquiv))

private theorem negativePoint_ne_one : negativePoint≠1 := by
  intro h
  have hp : positivePoint=1 := opposedFlagEquiv.injective
    (h.trans (map_one opposedFlagEquiv).symm)
  exact middleSquareRoot_ne_one (congrArg Subtype.val hp)

def negativeMiddleSquareRoot : CFSG.Models.Tits := negativePoint.val

theorem negativeMiddleSquareRoot_value : negativeMiddleSquareRoot=
    ambientAction 0 (oppositionFixed 0) middleSquareRoot := rfl

theorem negativeMiddleSquareRoot_original_value : negativeMiddleSquareRoot=
    derivedReeHom 0 (MulAut.conjNormal (oppositionFixed 0)
      ⟨(fourCycle 0)^2,square_mem_derived 0⟩) := by
  rw [negativeMiddleSquareRoot_value,middleSquareRoot_value,ambientAction_apply]

theorem negativeMiddleSquareRoot_square : negativeMiddleSquareRoot^2=1 :=
  congrArg Subtype.val negativePoint_square

theorem negativeMiddleSquareRoot_ne_one : negativeMiddleSquareRoot≠1 :=
  fun h => negativePoint_ne_one (Subtype.ext h)

theorem pairStabilizer_fixes_negativeMiddleSquareRoot (f : pairStabilizer) :
    f.val negativeMiddleSquareRoot=negativeMiddleSquareRoot := by
  let F : MulAut negativeIntrinsicFlag := CFSGInvariantSubgroupCoordinateImage.restrictAut
    negativeIntrinsicFlag f.val (pairStabilizer_preserves_negativeFlag f)
  have hF : F negativePoint=negativePoint :=
    CyclicFourUniqueInvolution.fixes_involution_of_embedding negativeEmbedding
      negativeEmbedding_injective (fourCycle 0) (fourCycle_order_four 0)
      negativeEmbedding_mem_cyclic F negativePoint negativePoint_square negativePoint_ne_one
  exact congrArg Subtype.val hF

end SymmetricSubgroupAsymptotics.CFSGTitsOpposedMiddleSquare
