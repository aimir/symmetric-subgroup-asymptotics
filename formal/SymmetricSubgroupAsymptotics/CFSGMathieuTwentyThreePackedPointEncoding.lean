import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeSelectedCodePointEncoding
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeSignedRelatorWords

/-! The SAME actual M23 normalized fibre for every valid443520-code
address. Raw computation uses only Nat selectors and the frozen degree22
packed maps. Valid-code conversion belongs solely to the proof shadow.
No fresh point rows, whole-group carrier, or finite capacity occur. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePackedPointEncoding
open CFSGMathieuTwentyThreeTailDecodeTransport CFSGMathieuTailPermutationExtension
open CFSGMathieuTwentyThreeNormalizedFibreChart CFSGMathieuTwentyThreeStabilizerTransversalCover
open CFSGMathieuTwentyThreeSelectedCodePointBinding
open CFSGMathieuTwentyTwoPackedPointMaps PermutationExtensionPointEncoding
open SignedPermutationWordPointEvaluation FixedProductSignedWordPointEncoding
open CFSGMathieuTwentyThreeSignedRelatorWords

private def point22 (p : Fin 23) (hp : p ≠ 22) : Fin 22 :=
  ⟨p.val,by
    have hlt := p.isLt
    have hne : p.val ≠ 22 := fun he => hp (Fin.ext he)
    omega⟩

private def first22 (i : First) : Fin 22 := point22 i.val i.property

private def second22 (j : Second) : CFSGMathieuTwentyTwoFiveTransversalCover.Second :=
  ⟨point22 j.val j.property.1,by
    intro he
    apply j.property.2
    exact Fin.ext (congrArg (fun q : Fin 22 => q.val) he)⟩

private def third22 (k : Third) : CFSGMathieuTwentyTwoFiveTransversalCover.Third :=
  ⟨point22 k.val k.property.1,by
    constructor
    · intro he
      apply k.property.2.1
      exact Fin.ext (congrArg (fun q : Fin 22 => q.val) he)
    · intro he
      apply k.property.2.2
      exact Fin.ext (congrArg (fun q : Fin 22 => q.val) he)⟩

private def fourth22 (l : Fourth) : CFSGMathieuTwentyTwoFiveTransversalCover.Fourth := by
  have hnot := Finset.mem_compl.mp l.property
  have hn : l.val ≠ 22 := by
    intro he
    apply hnot
    rw [he]
    decide +kernel
  refine ⟨point22 l.val hn,Finset.mem_compl.mpr ?_⟩
  intro hh
  have hs : l.val.val = 0 ∨ l.val.val = 1 ∨ l.val.val = 2 ∨
      l.val.val = 3 ∨ l.val.val = 4 ∨ l.val.val = 21 := by
    simpa only [CFSG.Certificates.Mathieu22.M22Certificates.SteinerSystem.blockB0,
      Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff] using hh
  apply hnot
  simp only [CFSG.Certificates.Mathieu23.M23Certificates.SteinerSystem.blockB0,
    Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff]
  change l.val.val = 0 ∨ l.val.val = 1 ∨ l.val.val = 2 ∨
    l.val.val = 3 ∨ l.val.val = 4 ∨ l.val.val = 21 ∨ l.val.val = 22
  omega

private def fifth22 (m : Fifth) : CFSGMathieuTwentyTwoFiveTransversalCover.Fifth := by
  have hs : m.val.val = 3 ∨ m.val.val = 4 ∨ m.val.val = 21 := by
    simpa only [Fin.ext_iff] using m.property
  have hn : m.val ≠ 22 := by
    intro he
    have hv := congrArg (fun q : Fin 23 => q.val) he
    omega
  refine ⟨point22 m.val hn,?_⟩
  change point22 m.val hn = 3 ∨ point22 m.val hn = 4 ∨ point22 m.val hn = 21
  simpa only [Fin.ext_iff] using hs

def toCode22 (c : Code23) : Code22 :=
  ((first22 c.1.1,second22 c.1.2),(third22 c.2.1,(fourth22 c.2.2.1,fifth22 c.2.2.2)))

theorem wordDecode_toCode22 (c : Code23) :
    extend23 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode (toCode22 c)).val) =
      (wordDecode c).val := by
  apply wordDecode_eq <;> rfl

def rawCandidateForward (i j k l m p : ℕ) : ℕ :=
  frameForward (rawExtension 22 (packedCandidateForward i j k l m) (frameInverse p))

def rawCandidateInverse (i j k l m p : ℕ) : ℕ :=
  frameForward (rawExtension 22 (packedCandidateInverse i j k l m) (frameInverse p))

private theorem tail_forward_point_eq (c : Code23) (p : Fin 23) :
    rawExtension 22 (packedCandidateForward c.1.1.val.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val) p.val = ((wordDecode c).val p).val := by
  have he := raw_forward_point_eq (toCode22 c) p
  change rawExtension 22 (packedCandidateForward c.1.1.val.val c.1.2.val.val c.2.1.val.val
    c.2.2.1.val.val c.2.2.2.val.val) p.val =
      (extend23 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode (toCode22 c)).val) p).val at he
  rw [wordDecode_toCode22] at he
  exact he

private theorem tail_inverse_point_eq (c : Code23) (p : Fin 23) :
    rawExtension 22 (packedCandidateInverse c.1.1.val.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val) p.val = ((wordDecode c).val.symm p).val := by
  have he := raw_inverse_point_eq (toCode22 c) p
  change rawExtension 22 (packedCandidateInverse c.1.1.val.val c.1.2.val.val c.2.1.val.val
    c.2.2.1.val.val c.2.2.2.val.val) p.val =
      ((extend23 ((CFSGMathieuTwentyTwoFiveTransversalCover.decode (toCode22 c)).val)).symm p).val at he
  rw [wordDecode_toCode22] at he
  exact he

private theorem conjugate_apply {X : Type*} (t h : Equiv.Perm X) (p : X) :
    (t*h*t⁻¹) p = t (h (t.symm p)) := rfl

private theorem conjugate_inverse_apply {X : Type*} (t h : Equiv.Perm X) (p : X) :
    (t*h*t⁻¹).symm p = t (h.symm (t.symm p)) := rfl

private theorem decode_coe (c : Code23) :
    (decodeAtZero c).val = conjugator.val * (wordDecode c).val * conjugator.val⁻¹ := by
  simp only [decodeAtZero,Subgroup.coe_mul,Subgroup.coe_inv]

theorem candidate_point_eq (c : Code23) (p : Fin 23) :
    rawCandidateForward c.1.1.val.val c.1.2.val.val c.2.1.val.val
        c.2.2.1.val.val c.2.2.2.val.val p.val = ((decodeAtZero c).val p).val ∧
      rawCandidateInverse c.1.1.val.val c.1.2.val.val c.2.1.val.val
        c.2.2.1.val.val c.2.2.2.val.val p.val = ((decodeAtZero c).val.symm p).val := by
  constructor
  · calc
      _ = (conjugator.val ((wordDecode c).val (conjugator.val.symm p))).val := by
        dsimp only [rawCandidateForward]
        rw [(frame_point_eq p).2,tail_forward_point_eq,(frame_point_eq _).1]
      _ = _ := by rw [decode_coe,conjugate_apply]
  · calc
      _ = (conjugator.val ((wordDecode c).val.symm (conjugator.val.symm p))).val := by
        dsimp only [rawCandidateInverse]
        rw [(frame_point_eq p).2,tail_inverse_point_eq,(frame_point_eq _).1]
      _ = _ := by rw [decode_coe,conjugate_inverse_apply]

def rawRelator (r i j k l m p : ℕ) : ℕ :=
  applyWord (rawCandidateForward i j k l m) (rawCandidateInverse i j k l m)
    productForward productInverse (fixedProductWord (relatorWord r)) p

theorem accepts_pointwise (c : Code23)
    (hc : CFSGMathieuTwentyThreeProductNecessaryRelations.Accepts (decodeAtZero c).val)
    (r : Fin 9) (p : Fin 23) :
    rawRelator r.val c.1.1.val.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val p.val = p.val := by
  apply CFSGMathieuTwentyThreeSignedRelatorWords.raw_relator_point
    (decodeAtZero c).val
  · exact fun q => (candidate_point_eq c q).1
  · exact fun q => (candidate_point_eq c q).2
  · exact fun q => (CFSGMathieuTwentyThreeSelectedCodePointEncoding.fixedProduct_point_eq q).1
  · exact fun q => (CFSGMathieuTwentyThreeSelectedCodePointEncoding.fixedProduct_point_eq q).2
  · exact hc

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePackedPointEncoding
