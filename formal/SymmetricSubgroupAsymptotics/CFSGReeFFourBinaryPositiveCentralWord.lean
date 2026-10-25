import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveCentre

/-! Decode the unique nonidentity positive centre element in the ORIGINAL
fixed group. The central code has only its bit7, which is the square of
one whole middle block. No equality is reflected from norm matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveCentralWord
open CFSGReeFFourBinaryPositiveCentre CFSGReeFFourBinaryPositiveCommonCentralizer
open CFSGReeFFourBinaryPositiveFinalConstraint CFSGReeFFourBinaryOrderedBooleanParameters
open CFSGReeFFourBinaryOrderedRootWords CFSGFFourNormPrimeFieldWords
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourInversionPeelingWords
open CFSGReeFFourDerivedAmbientHom CFSGOpposedPeelingOrderedParameters
open CFSGOpposedSubgroupPeelingChain

private theorem ordered_eight_single_four {G : Type*} [Group G]
    (w : ℕ → G) (x : G) :
    orderedProduct w 8 ![1,1,1,1,x,1,1,1]=
      (wordPrefix w 4)⁻¹*x*wordPrefix w 4 := by
  simp [orderedProduct,mul_assoc]

def centralWord : originalModelFixed 0 :=
  (wordPrefix (step 0 true) 4)⁻¹*(fourCycle 0)^2*wordPrefix (step 0 true) 4

theorem central_code_word_value (b : Fin 12 → Bool) (hb : CentralCode b) :
    wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=
      if b 7 then centralWord.val else 1 := by
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  have h4 := hb 4 (by decide)
  have h5 := hb 5 (by decide)
  have h6 := hb 6 (by decide)
  have h8 := hb 8 (by decide)
  have h9 := hb 9 (by decide)
  have h10 := hb 10 (by decide)
  have h11 := hb 11 (by decide)
  have hp : (fun j : Fin 8 => (baseElement 0 j.val)^
      (exponentFunction b j.val))=
      ![1,1,1,1,(fourCycle 0)^(2*(b 7).toNat),1,1,1] := by
    funext j
    fin_cases j <;> simp [exponentFunction,parameterExponents,baseElement,
      h0,h1,h2,h3,h4,h5,h6,h8,h9,h10,h11]
  have he := ordered_letters_value 0 (exponentFunction b) 8
  rw [hp,ordered_eight_single_four] at he
  cases h7 : b 7 <;> simpa [h7,centralWord] using he

theorem center_nonidentity_eq (z : Subgroup.center (derivedPositive 0))
    (hz : z.val.val.val≠1) : z.val.val.val=centralWord := by
  let u : CommonCentralizer := centerToCommon z
  obtain ⟨b,hb,hc⟩ := exists_positive_central_code u.val u.property.1
    u.property.2.1 u.property.2.2.1 u.property.2.2.2
  have hv := hb.symm.trans (central_code_word_value b hc)
  by_cases h7 : b 7=true
  · apply Subtype.ext
    simpa only [h7,if_true] using hv
  · have hfalse : b 7=false := Bool.eq_false_of_not_eq_true h7
    have hu : u.val=1 := Subtype.ext (by simpa only [hfalse,if_false] using hv)
    exact False.elim (hz hu)

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveCentralWord
