import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeSelectedCodePointBinding
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeTailDecodeTransport
import SymmetricSubgroupAsymptotics.CFSGMathieuPrimeProductNecessaryRelations

/-! Actual typed shadows for the ONE code(1,2,3,6,4). The shared M22 packed
maps are transported through the genuine permutation extension and the
original checked M23 frame. The product is the represented pinned product.
There is no acceptance statement, group recovery, or finite capacity. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeSelectedCodePointEncoding
open CFSGMathieuTwentyThreeTailDecodeTransport
open CFSGMathieuTailPermutationExtension
open CFSGMathieuTwentyThreeSelectedCodePointBinding
open CFSGMathieuTwentyThreeNormalizedFibreChart
open CFSGMathieuTwentyThreeActualRepresentation CFSGMathieuTwentyThreePresentationWords

def selectedCode22 : Code22 :=
  ((1,⟨2,by decide⟩),(⟨3,by decide⟩,(⟨6,by decide⟩,⟨4,by decide⟩)))

def selectedCode23 : Code23 :=
  ((⟨1,by decide⟩,⟨2,by decide⟩),(⟨3,by decide⟩,(⟨6,by decide⟩,⟨4,by decide⟩)))

private theorem selected_tail_eq :
    extend23 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode selectedCode22).val) =
      (CFSGMathieuTwentyThreeStabilizerTransversalCover.wordDecode selectedCode23).val :=
  wordDecode_eq selectedCode22 selectedCode23 rfl rfl rfl rfl rfl

theorem tail_forward_point_eq (p : Fin 23) :
    rawTailForward p.val =
      ((CFSGMathieuTwentyThreeStabilizerTransversalCover.wordDecode selectedCode23).val p).val := by
  have he := raw_forward_point_eq selectedCode22 p
  change rawTailForward p.val =
    (extend23 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode selectedCode22).val) p).val at he
  rw [selected_tail_eq] at he
  exact he

theorem tail_inverse_point_eq (p : Fin 23) :
    rawTailInverse p.val =
      ((CFSGMathieuTwentyThreeStabilizerTransversalCover.wordDecode selectedCode23).val.symm p).val := by
  have he := raw_inverse_point_eq selectedCode22 p
  change rawTailInverse p.val =
    ((extend23 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode selectedCode22).val)).symm p).val at he
  rw [selected_tail_eq] at he
  exact he

private theorem conjugate_apply {X : Type*} (t h : Equiv.Perm X) (p : X) :
    (t*h*t⁻¹) p = t (h (t.symm p)) := rfl

private theorem conjugate_inverse_apply {X : Type*} (t h : Equiv.Perm X) (p : X) :
    (t*h*t⁻¹).symm p = t (h.symm (t.symm p)) := rfl

private theorem selected_decode_coe :
    (decodeAtZero selectedCode23).val = conjugator.val *
      (CFSGMathieuTwentyThreeStabilizerTransversalCover.wordDecode selectedCode23).val *
        conjugator.val⁻¹ := by
  simp only [decodeAtZero,Subgroup.coe_mul,Subgroup.coe_inv]

theorem candidate_point_eq (p : Fin 23) :
    cachedCandidateForward p.val = ((decodeAtZero selectedCode23).val p).val ∧
      cachedCandidateInverse p.val = ((decodeAtZero selectedCode23).val.symm p).val := by
  constructor
  · calc
      _ = rawCandidateForward p.val := (candidate_cache_eq p).1
      _ = (conjugator.val
          ((CFSGMathieuTwentyThreeStabilizerTransversalCover.wordDecode selectedCode23).val
            (conjugator.val.symm p))).val := by
        dsimp only [rawCandidateForward]
        rw [(frame_point_eq p).2,tail_forward_point_eq,(frame_point_eq _).1]
      _ = _ := by rw [selected_decode_coe,conjugate_apply]
  · calc
      _ = rawCandidateInverse p.val := (candidate_cache_eq p).2
      _ = (conjugator.val
          ((CFSGMathieuTwentyThreeStabilizerTransversalCover.wordDecode selectedCode23).val.symm
            (conjugator.val.symm p))).val := by
        dsimp only [rawCandidateInverse]
        rw [(frame_point_eq p).2,tail_inverse_point_eq,(frame_point_eq _).1]
      _ = _ := by rw [selected_decode_coe,conjugate_inverse_apply]

private theorem fixedProduct_eq :
    CFSGMathieuTwentyThreeProductNecessaryRelations.fixedProduct = xPermutation*yPermutation := by
  change permutationRepresentation
    ((PresentedGroup.of (0 : Fin 2))*(PresentedGroup.of (1 : Fin 2))) = _
  rw [map_mul,permutationRepresentation_of_zero,permutationRepresentation_of_one]

theorem fixedProduct_point_eq (p : Fin 23) :
    productForward p.val =
        (CFSGMathieuTwentyThreeProductNecessaryRelations.fixedProduct p).val ∧
      productInverse p.val =
        (CFSGMathieuTwentyThreeProductNecessaryRelations.fixedProduct.symm p).val := by
  simpa only [fixedProduct_eq] using
    CFSGMathieuTwentyThreeSelectedCodePointBinding.product_point_eq p

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeSelectedCodePointEncoding
