import SymmetricSubgroupAsymptotics.CFSGTitsOuterImageOrderedConstraints
import SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailDecodedConditions
import SymmetricSubgroupAsymptotics.CFSGReeFFourPackedFixedWordSemantics
import SymmetricSubgroupAsymptotics.CFSGTitsSimpleNormFaithfulness

/-! Necessary compact conditions for the SAME actual source u and
ordered word. Nonidentity uses the genuine norm action's proved
faithfulness under the existing simple-Tits hypothesis; equalities use
one-way original-word transport. No automorphism is extended. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsOuterImagePackedConditions
open CFSGTitsOuterImageOrderedConstraints CFSGTitsIntrinsicMiddleRadical
open CFSGTitsAmbientPairAlignment CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourOrderedTailMaskCoordinates CFSGReeFFourBinaryOrderedBooleanParameters
open CFSGReeFFourBinaryOrderedRootWords CFSGReeFFourBinaryOrderedPrefixMatrices
open CFSGReeFFourBinaryOrderedMatrixData CFSGFFourNormPrimeFieldWords
open CFSGFFourNormSparseWordMatrix CFSGFFourNormPrimeFieldMatrixTransport
open CFSGReeFFourPackedTailSixteenPilot CFSGReeFFourPackedTailMatrixSemantics
open CFSGReeFFourPackedTailDecodedConditions CFSGReeFFourPackedFixedWordSemantics
open CFSGReeFFourPackedReflectionConstants CFSGTitsSimpleNormFaithfulness
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourOuterCentralizingReflection
open BinaryPackedMatrix
open CFSGReeFFourSignedOuterOddProduct
private abbrev D := commutator (originalModelFixed 0)
private abbrev opposite : MulAut D := MulAut.conjNormal (oppositionFixed 0)
private def forget : D →* CFSG.Models.Chevalley.Model CartanMatrix.F₄ (Field 0) :=
  (originalModelFixed 0).subtype.comp D.subtype

private theorem map_power_one {G H : Type*} [Group G] [Monoid H]
    (f : G →* H) (u : G) (n : ℕ) (h : u^n=1) : (f u)^n=1 :=
  (map_pow f u n).symm.trans ((congrArg f h).trans (map_one f))

private theorem cube_mul {M : Type*} [Monoid M] (a : M) (h : a^3=1) : a*a*a=1 := by
  simpa only [pow_succ,pow_zero,mul_one,one_mul] using h

def sourceLetters (c : Fin 1024) : List Letter :=
  orderedLetters (exponentFunction (tailBits c)) 8

def opposedLetters (c : Fin 1024) : List Letter :=
  prefixLetters 8++sourceLetters c++(prefixLetters 8).reverse++sourceLetters c

private theorem source_matrix (c : Fin 1024) :
    decode (packedChart c)=wordMatrix (ZMod 2) (sourceLetters c) :=
  packedChart_eq_wordMatrix c

private theorem back_eight : backMatrix 8=prefixMatrix 8 := by
  decide +kernel

private theorem opposed_matrix (c : Fin 1024) :
    decode (opposedProduct c)=wordMatrix (ZMod 2) (opposedLetters c) := by
  simp only [opposedProduct,decode_mul,opposedLetters,wordMatrix_append]
  have hb : wordMatrix (ZMod 2) (prefixLetters 8).reverse=backMatrix 8 :=
    reversed_prefix_matrix 0 8
  have hp : wordMatrix (ZMod 2) (prefixLetters 8)=prefixMatrix 8 := prefix_matrix 8
  rw [source_matrix,decode_packedOpposition,hb,hp,back_eight]

private theorem opposed_value (u : D) (c : Fin 1024)
    (hw : wordValue (Field 0) (sourceLetters c)=u.val.val) :
    wordValue (Field 0) (opposedLetters c)=(opposite u*u).val.val := by
  simp only [opposedLetters,wordValue_append,reversed_letters_value,
    oppositionLetters_value,hw]; rfl

private theorem matrix_ne_one [IsSimpleGroup CFSG.Models.Tits]
    (u : D) (s : List Letter)
    (hw : wordValue (Field 0) s=u.val.val) (hn : u≠1) :
    wordMatrix (ZMod 2) s≠1 := by
  intro h
  apply hn
  exact eq_of_primeField_wordMatrix_eq u 1 s [] hw.symm rfl h

private theorem matrix_pow_one (s : List Letter) (n : ℕ)
    (h : (wordValue (Field 0) s)^n=1) :
    (wordMatrix (ZMod 2) s)^n=1 := by
  have hv : wordValue (Field 0) ((List.replicate n s).flatten)=
      wordValue (Field 0) [] := (repeated_letters_value (Field 0) s n).trans h
  have hm := wordMatrix_eq_of_wordValue_eq (Field 0) _ _ hv
  change wordMatrix (ZMod 2) ((List.replicate n s).flatten)=1 at hm
  rwa [repeated_word_matrix] at hm

theorem packed_conditions_of_source [IsSimpleGroup CFSG.Models.Tits]
    (u : D) (c : Fin 1024)
    (hw : wordValue (Field 0) (sourceLetters c)=u.val.val)
    (hn : u≠1) (hs : u^2=1)
    (hc : Commute (reflectionWord 0) u.val)
    (hpn : opposite u*u≠1) (hps : (opposite u*u)^3=1) :
    packedAdmissible c=true := by
  apply packedAdmissible_of_decoded c
  · rw [source_matrix]
    exact matrix_ne_one u (sourceLetters c) hw hn
  · rw [source_matrix,←pow_two]
    apply matrix_pow_one
    rw [hw]
    exact congrArg (fun d : D=>d.val.val) hs
  · rw [source_matrix,←reflectionLetters_matrix]
    have hv : Commute (wordValue (Field 0) reflectionLetters)
        (wordValue (Field 0) (sourceLetters c)) := by
      rw [reflectionLetters_value,hw]
      exact hc.map (originalModelFixed 0).subtype
    exact (wordMatrix_commute_of_wordValue_commute (Field 0) _ _ hv).eq.symm
  · rw [opposed_matrix]
    exact matrix_ne_one (opposite u*u) (opposedLetters c) (opposed_value u c hw) hpn
  · rw [opposed_matrix]
    have hm : (wordMatrix (ZMod 2) (opposedLetters c))^3=1 := by
      apply matrix_pow_one
      have hword : wordValue (Field 0) (opposedLetters c)=forget (opposite u*u) :=
        opposed_value u c hw
      exact (congrArg (fun d : CFSG.Models.Chevalley.Model CartanMatrix.F₄ (Field 0) =>
        d^3) hword).trans (map_power_one forget (opposite u*u) 3 hps)
    exact cube_mul (M:=Matrix (Fin 26) (Fin 26) (ZMod 2))
      (wordMatrix (ZMod 2) (opposedLetters c)) hm

theorem exists_admissible_source [IsSimpleGroup CFSG.Models.Tits] (f : pairStabilizer) :
    ∃c : Fin 1024,∃u : sourceIntersection,
      derivedReeHom 0 u.val=f.val (originalOuterRoot 0) ∧
      wordValue (Field 0) (sourceLetters c)=u.val.val.val ∧
      packedAdmissible c=true := by
  obtain ⟨u,c,hu,hw,hn,hs,hc,hpn,hps⟩ := exists_source_mask f
  exact ⟨c,u,hu,hw,packed_conditions_of_source u.val c hw hn hs hc hpn hps⟩

end SymmetricSubgroupAsymptotics.CFSGTitsOuterImagePackedConditions
