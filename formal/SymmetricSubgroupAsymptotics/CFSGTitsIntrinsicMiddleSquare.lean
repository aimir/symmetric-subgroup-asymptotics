import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleFlag
import SymmetricSubgroupAsymptotics.CyclicFourUniqueInvolution
import SymmetricSubgroupAsymptotics.CFSGInvariantSubgroupCoordinateImage
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareCommutator

/-! An intrinsic second positive involution is recovered from the
opposed-centre reflection flag. The flag embeds in the ORIGINAL middle
C4 but can itself have order two. Target automorphisms are restricted
only to the intrinsic Tits flag, never lifted to the ambient fixed group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleSquare
open CFSGTitsIntrinsicMiddleFlag CFSGTitsAmbientPairAlignment
open CFSGReeFFourBinaryReflectionMiddleFlag CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourBinaryMiddleGenerators CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourMiddleSquareCommutator CFSGReeFFourMiddleFixedSubgroup
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourFixedDerivedInversionFacts
open CFSGReeFFourFixedAmbientHom
private abbrev D := commutator (originalModelFixed 0)
private instance fixedFinite : Finite (originalModelFixed 0) :=
  Finite.of_injective (fixedAmbientHom 0) (fixedAmbientHom_injective 0)

private def originalEmbedding : reflectionIntersection →* originalModelFixed 0 :=
  D.subtype.comp reflectionIntersection.subtype

private def flagEmbedding : intrinsicFlag →* originalModelFixed 0 :=
  originalEmbedding.comp flagEquiv.symm.toMonoidHom

private theorem flagEmbedding_injective : Function.Injective flagEmbedding := by
  intro x y h
  apply flagEquiv.symm.injective
  exact Subtype.ext (Subtype.ext h)

private theorem flagEmbedding_mem_cyclic (x : intrinsicFlag) :
    flagEmbedding x∈Subgroup.zpowers (fourCycle 0) := by
  let z : reflectionIntersection := flagEquiv.symm x
  have hm : z.val∈(middleFixedSubgroup 0).comap D.subtype :=
    Eq.mp (congrArg (fun U : Subgroup D => z.val∈U)
      reflectionIntersection_eq_restricted_middle) z.property
  change (z.val : originalModelFixed 0)∈Subgroup.zpowers (fourCycle 0)
  rw [←middleFixed_zero_eq_zpowers]
  exact hm

private theorem square_ne_one {G : Type*} [Group G] (y : G) (hy : orderOf y=4) : y^2≠1 := by
  intro h
  have hd := orderOf_dvd_of_pow_eq_one h
  rw [hy] at hd
  norm_num at hd

private def squareSource : D := ⟨(fourCycle 0)^2,square_mem_derived 0⟩

private theorem squareSource_mem_flag : squareSource∈reflectionIntersection := by
  have hm : squareSource∈(middleFixedSubgroup 0).comap D.subtype := by
    change (fourCycle 0)^2∈middleFixedSubgroup 0
    rw [middleFixed_zero_eq_zpowers]
    exact (Subgroup.zpowers (fourCycle 0)).pow_mem (Subgroup.mem_zpowers _) 2
  exact Eq.mpr (congrArg (fun U : Subgroup D => squareSource∈U)
    reflectionIntersection_eq_restricted_middle) hm

private def squarePoint : intrinsicFlag := flagEquiv ⟨squareSource,squareSource_mem_flag⟩

private theorem squarePoint_square : squarePoint^2=1 := by
  have hs : (⟨squareSource,squareSource_mem_flag⟩ : reflectionIntersection)^2=1 :=
    Subtype.ext (Subtype.ext (middle_square_square 0))
  exact (map_pow flagEquiv _ 2).symm.trans ((congrArg flagEquiv hs).trans (map_one flagEquiv))

private theorem squarePoint_ne_one : squarePoint≠1 := by
  intro h
  have he : (⟨squareSource,squareSource_mem_flag⟩ : reflectionIntersection)=1 :=
    flagEquiv.injective (h.trans (map_one flagEquiv).symm)
  exact square_ne_one (fourCycle 0) (fourCycle_order_four 0)
    (congrArg (fun z : reflectionIntersection => (z.val : originalModelFixed 0)) he)

def middleSquareRoot : CFSG.Models.Tits := squarePoint.val

theorem middleSquareRoot_value :
    middleSquareRoot=derivedReeHom 0 ⟨(fourCycle 0)^2,square_mem_derived 0⟩ := rfl

theorem middleSquareRoot_square : middleSquareRoot^2=1 := congrArg Subtype.val squarePoint_square

theorem middleSquareRoot_ne_one : middleSquareRoot≠1 :=
  fun h => squarePoint_ne_one (Subtype.ext h)

theorem pairStabilizer_fixes_middleSquareRoot (f : pairStabilizer) :
    f.val middleSquareRoot=middleSquareRoot := by
  let F : MulAut intrinsicFlag := CFSGInvariantSubgroupCoordinateImage.restrictAut
    intrinsicFlag f.val (pairStabilizer_preserves_intrinsicFlag f)
  have hF : F squarePoint=squarePoint :=
    CyclicFourUniqueInvolution.fixes_involution_of_embedding flagEmbedding
      flagEmbedding_injective (fourCycle 0) (fourCycle_order_four 0)
      flagEmbedding_mem_cyclic F squarePoint squarePoint_square squarePoint_ne_one
  exact congrArg Subtype.val hF

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleSquare
