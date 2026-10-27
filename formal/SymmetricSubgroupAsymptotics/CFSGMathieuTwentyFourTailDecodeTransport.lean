import SymmetricSubgroupAsymptotics.CFSGMathieuTailWordTransport
import SymmetricSubgroupAsymptotics.PermutationExtensionPointEncoding
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPointMaps
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTwoPointTailCover

/-! Source-only adapter: the two charts use identical addresses for their shared tail.
Matching literal addresses transport the whole actual decoded permutation,
then the already checked packed forward/inverse maps. These equalities
assert no abstract model identification or automorphism extension. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTailDecodeTransport
open CFSGMathieuTailPermutationExtension CFSGMathieuTailWordTransport
open CFSGMathieuTwentyTwoPackedPointMaps PermutationExtensionPointEncoding

abbrev Code22 := CFSGMathieuTwentyTwoFiveTransversalCover.Code
abbrev Code24 := CFSGMathieuTwentyFourTwoPointTailCover.Code

theorem decode_eq (c : Code22) (d : Code24)
    (hi : c.1.1.val = d.1.val.val)
    (hj : c.1.2.val.val = d.2.1.val.val)
    (hk : c.2.1.val.val = d.2.2.1.val.val)
    (hl : c.2.2.1.val.val = d.2.2.2.1.val.val)
    (hm : c.2.2.2.val.val = d.2.2.2.2.val.val) :
    extend24 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val) =
      (CFSGMathieuTwentyFourTwoPointTailCover.decode d).val := by
  have hi' : c.1.1.castLE (by decide : 22 ≤ 24) = d.1.val := Fin.ext hi
  have hj' : c.1.2.val.castLE (by decide : 22 ≤ 24) = d.2.1.val := Fin.ext hj
  have hk' : c.2.1.val.castLE (by decide : 22 ≤ 24) = d.2.2.1.val := Fin.ext hk
  have hl' : c.2.2.1.val.castLE (by decide : 22 ≤ 24) = d.2.2.2.1.val := Fin.ext hl
  have hm' : c.2.2.2.val.castLE (by decide : 22 ≤ 24) = d.2.2.2.2.val := Fin.ext hm
  have h1 := word24_eval
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.orbitZeroWord c.1.1)
  rw [first_word24,hi'] at h1
  have h2 := word24_eval
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.zeroStabilizerWord c.1.2.val)
  rw [second_word24,hj'] at h2
  have h3 := word24_eval
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.zeroOneStabilizerWord c.2.1.val)
  rw [third_word24,hk'] at h3
  have h4 := word24_eval
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.levelFourWord c.2.2.1.val)
  rw [fourth_word24,hl'] at h4
  have h5 := word24_eval
    (CFSG.Certificates.Mathieu22.M22Certificates.StabilizerChain.levelFiveWord c.2.2.2.val)
  rw [fifth_word24,hm'] at h5
  change extend24
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

/-- Five separate small address checks; never a 443520-code reduction. -/
theorem exists_same_addresses (d : Code24) :
    ∃ c : Code22, c.1.1.val=d.1.val.val ∧
      c.1.2.val.val=d.2.1.val.val ∧ c.2.1.val.val=d.2.2.1.val.val ∧
      c.2.2.1.val.val=d.2.2.2.1.val.val ∧ c.2.2.2.val.val=d.2.2.2.2.val.val := by
  have h0 : ∀ i : CFSGMathieuTwentyFourTwoPointTailCover.First,
      ∃ j : Fin 22, j.val=i.val.val := by decide +kernel
  have h1 : ∀ i : CFSGMathieuTwentyFourTwoPointTailCover.Second,
      ∃ j : CFSGMathieuTwentyTwoFiveTransversalCover.Second,
        j.val.val=i.val.val := by decide +kernel
  have h2 : ∀ i : CFSGMathieuTwentyFourTwoPointTailCover.Third,
      ∃ j : CFSGMathieuTwentyTwoFiveTransversalCover.Third,
        j.val.val=i.val.val := by decide +kernel
  have h3 : ∀ i : CFSGMathieuTwentyFourTwoPointTailCover.Fourth,
      ∃ j : CFSGMathieuTwentyTwoFiveTransversalCover.Fourth,
        j.val.val=i.val.val := by decide +kernel
  have h4 : ∀ i : CFSGMathieuTwentyFourTwoPointTailCover.Fifth,
      ∃ j : CFSGMathieuTwentyTwoFiveTransversalCover.Fifth,
        j.val.val=i.val.val := by decide +kernel
  obtain ⟨i,hi⟩ := h0 d.1
  obtain ⟨j,hj⟩ := h1 d.2.1
  obtain ⟨k,hk⟩ := h2 d.2.2.1
  obtain ⟨l,hl⟩ := h3 d.2.2.2.1
  obtain ⟨m,hm⟩ := h4 d.2.2.2.2
  exact ⟨((i,j),(k,(l,m))),hi,hj,hk,hl,hm⟩

theorem decode_has_shared_code (d : Code24) : ∃ c : Code22,
    extend24 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val)=
      (CFSGMathieuTwentyFourTwoPointTailCover.decode d).val := by
  obtain ⟨c,hi,hj,hk,hl,hm⟩ := exists_same_addresses d
  exact ⟨c,decode_eq c d hi hj hk hl hm⟩

theorem raw_forward_point_eq (c : Code22) (p : Fin 24) :
    rawExtension 22 (packedCandidateForward c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val) p.val =
      (extend24 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val) p).val := by
  apply rawExtension_point_eq (by decide : 22 ≤ 24)
  intro q
  have he := candidateForward_point_eq c q
  rw [CFSGMathieuTwentyTwoScalarRelationWords.candidateForward_eq] at he
  exact he

theorem raw_inverse_point_eq (c : Code22) (p : Fin 24) :
    rawExtension 22 (packedCandidateInverse c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val) p.val =
      ((extend24 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val)).symm p).val := by
  have he : (extend24 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val)).symm =
      extend24 (((CFSGMathieuTwentyTwoFiveTransversalCover.decode c).val).symm) :=
    (map_inv extend24 _).symm
  rw [he]
  apply rawExtension_point_eq (by decide : 22 ≤ 24)
  intro q
  have heq := candidateInverse_point_eq c q
  rw [CFSGMathieuTwentyTwoScalarRelationWords.candidateInverse_eq] at heq
  exact heq

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourTailDecodeTransport
