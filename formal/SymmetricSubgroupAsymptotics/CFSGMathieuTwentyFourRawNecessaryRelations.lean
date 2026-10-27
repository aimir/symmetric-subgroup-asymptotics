import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourPackedFrameRows
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFixedProductRelations

/-! All-Code22 raw-Nat necessary relators using exactly the already checked
M22 packed tail maps extended by two fixed points. Only the six genuine
M24 frame/x/product rows are new finite data. No capacity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourRawNecessaryRelations
open CFSGMathieuTwentyFourPackedFrameRows
open CFSGMathieuTwentyFourTailDecodeTransport CFSGMathieuTwentyFourSharedSwapChart
open CFSGMathieuTwentyFourTwoPointTailCover CFSGMathieuTwentyFourFixedProductRelations
open CFSGMathieuTwentyFourActualRepresentation CFSGMathieuTwentyFourSwapFibreOuterReduction
open CFSGMathieuTwentyTwoPackedPointMaps (packedCandidateForward packedCandidateInverse)
open PermutationExtensionPointEncoding
open SignedPermutationWordPointEvaluation SignedPermutationWordPointEncoding

private theorem frame_forward_apply (x t k : Equiv.Perm (Fin 24)) (p : Fin 24) :
    (x*t*k*t⁻¹) p=x (t (k (t.symm p))) := rfl

private theorem frame_inverse_apply (x t k : Equiv.Perm (Fin 24)) (p : Fin 24) :
    (x*t*k*t⁻¹).symm p=t (k.symm (t.symm (x.symm p))) := rfl

def rawCandidateForward (i j k l m p : ℕ) : ℕ :=
  packedGet xRow (packedGet frameRow
    (rawExtension 22 (packedCandidateForward i j k l m) (packedGet frameInverseRow p)))

def rawCandidateInverse (i j k l m p : ℕ) : ℕ :=
  packedGet frameRow (rawExtension 22 (packedCandidateInverse i j k l m)
    (packedGet frameInverseRow (packedGet xInverseRow p)))

theorem candidate_forward_point_eq (c : Code22) (p : Fin 24) :
    rawCandidateForward c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val p.val=(sharedSwapDecode c p).val := by
  unfold rawCandidateForward
  rw [(frame_point_binding p).2,raw_forward_point_eq]
  rw [(frame_point_binding _).1,(x_point_binding _).1]
  exact congrArg Fin.val (frame_forward_apply
    CFSGMathieuTwentyFourPresentationWords.x.val transport.val
    (CFSGMathieuTailPermutationExtension.extend24
      ((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val)) p).symm

theorem candidate_inverse_point_eq (c : Code22) (p : Fin 24) :
    rawCandidateInverse c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val p.val=((sharedSwapDecode c).symm p).val := by
  unfold rawCandidateInverse
  rw [(x_point_binding p).2,(frame_point_binding _).2,raw_inverse_point_eq,
    (frame_point_binding _).1]
  exact congrArg Fin.val (frame_inverse_apply
    CFSGMathieuTwentyFourPresentationWords.x.val transport.val
    (CFSGMathieuTailPermutationExtension.extend24
      ((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val)) p).symm

def rawScalarRelation (r : Fin 7) (c : Code22) (p : ℕ) : ℕ :=
  applyWord (packedGet productRow) (packedGet productInverseRow)
    (rawCandidateForward c.1.1.val c.1.2.val.val c.2.1.val.val c.2.2.1.val.val c.2.2.2.val.val)
    (rawCandidateInverse c.1.1.val c.1.2.val.val c.2.1.val.val c.2.2.1.val.val c.2.2.2.val.val)
    (relationWord r) p

theorem rawScalarRelation_point_eq (r : Fin 7) (c : Code22) (p : Fin 24) :
    rawScalarRelation r c p.val=
      (relationValue r (permutationRepresentation product) (sharedSwapDecode c) p).val := by
  unfold rawScalarRelation
  rw [applyWord_encoding (fun q : Fin 24 => q.val)
    (permutationRepresentation product) (permutationRepresentation product).symm
    (sharedSwapDecode c) (sharedSwapDecode c).symm
    (packedGet productRow) (packedGet productInverseRow)
    (rawCandidateForward c.1.1.val c.1.2.val.val c.2.1.val.val c.2.2.1.val.val c.2.2.2.val.val)
    (rawCandidateInverse c.1.1.val c.1.2.val.val c.2.1.val.val c.2.2.1.val.val c.2.2.2.val.val)
    (fun q => (product_point_binding q).1) (fun q => (product_point_binding q).2)
    (candidate_forward_point_eq c) (candidate_inverse_point_eq c)]
  rw [applyWord_eq,eval_relationWord]

theorem accepts_rawScalarRelation (c : Code22) (hc : Accepts c) (r : Fin 7) (p : Fin 24) :
    rawScalarRelation r c p.val=p.val := by
  rw [rawScalarRelation_point_eq,hc r]
  rfl

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourRawNecessaryRelations
