import SymmetricSubgroupAsymptotics.CFSGMathieuTailWordTransport
import SymmetricSubgroupAsymptotics.PermutationExtensionPointEncoding
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPointMaps
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeStabilizerTransversalCover

/-! The two checked charts use identical addresses for their shared tail.
Matching literal addresses transport the whole actual decoded permutation,
then the already checked packed forward/inverse maps. These equalities
assert no abstract model identification or automorphism extension. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeTailDecodeTransport
open CFSGMathieuTailPermutationExtension CFSGMathieuTailWordTransport
open CFSGMathieuTwentyTwoPackedPointMaps PermutationExtensionPointEncoding

abbrev Code22 := CFSGMathieuTwentyTwoFiveTransversalCover.Code
abbrev Code23 := CFSGMathieuTwentyThreeStabilizerTransversalCover.Code

theorem wordDecode_eq (c : Code22) (d : Code23)
    (hi : c.1.1.val = d.1.1.val.val)
    (hj : c.1.2.val.val = d.1.2.val.val)
    (hk : c.2.1.val.val = d.2.1.val.val)
    (hl : c.2.2.1.val.val = d.2.2.1.val.val)
    (hm : c.2.2.2.val.val = d.2.2.2.val.val) :
    extend23 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val) =
      (CFSGMathieuTwentyThreeStabilizerTransversalCover.wordDecode d).val := by
  have hi' : c.1.1.castLE (by decide : 22 ≤ 23) = d.1.1.val := Fin.ext hi
  have hj' : c.1.2.val.castLE (by decide : 22 ≤ 23) = d.1.2.val := Fin.ext hj
  have hk' : c.2.1.val.castLE (by decide : 22 ≤ 23) = d.2.1.val := Fin.ext hk
  have hl' : c.2.2.1.val.castLE (by decide : 22 ≤ 23) = d.2.2.1.val := Fin.ext hl
  have hm' : c.2.2.2.val.castLE (by decide : 22 ≤ 23) = d.2.2.2.val := Fin.ext hm
  have h1 := word23_eval
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.orbitZeroWord c.1.1)
  rw [first_word23,hi'] at h1
  have h2 := word23_eval
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.zeroStabilizerWord c.1.2.val)
  rw [second_word23,hj'] at h2
  have h3 := word23_eval
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.zeroOneStabilizerWord c.2.1.val)
  rw [third_word23,hk'] at h3
  have h4 := word23_eval
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.levelFourWord c.2.2.1.val)
  rw [fourth_word23,hl'] at h4
  have h5 := word23_eval
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.levelFiveWord c.2.2.2.val)
  rw [fifth_word23,hm'] at h5
  change extend23
    (CFSG.Certificates.Mathieu22.M22Certificates.Word.eval
        (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.orbitZeroWord c.1.1) *
      CFSG.Certificates.Mathieu22.M22Certificates.Word.eval
        (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.zeroStabilizerWord c.1.2.val) *
      CFSG.Certificates.Mathieu22.M22Certificates.Word.eval
        (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.zeroOneStabilizerWord c.2.1.val) *
      CFSG.Certificates.Mathieu22.M22Certificates.Word.eval
        (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.levelFourWord c.2.2.1.val) *
      CFSG.Certificates.Mathieu22.M22Certificates.Word.eval
        (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.levelFiveWord c.2.2.2.val)) = _
  simp only [map_mul,h1,h2,h3,h4,h5]
  rfl

theorem raw_forward_point_eq (c : Code22) (p : Fin 23) :
    rawExtension 22 (packedCandidateForward c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val) p.val =
      (extend23 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val) p).val := by
  apply rawExtension_point_eq (by decide : 22 ≤ 23)
  intro q
  have he := candidateForward_point_eq c q
  rw [CFSGMathieuTwentyTwoScalarRelationWords.candidateForward_eq] at he
  exact he

theorem raw_inverse_point_eq (c : Code22) (p : Fin 23) :
    rawExtension 22 (packedCandidateInverse c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val) p.val =
      ((extend23 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val)).symm p).val := by
  have he : (extend23 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val)).symm =
      extend23 (((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val).symm) :=
    (map_inv extend23 _).symm
  rw [he]
  apply rawExtension_point_eq (by decide : 22 ≤ 23)
  intro q
  have heq := candidateInverse_point_eq c q
  rw [CFSGMathieuTwentyTwoScalarRelationWords.candidateInverse_eq] at heq
  exact heq

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeTailDecodeTransport
