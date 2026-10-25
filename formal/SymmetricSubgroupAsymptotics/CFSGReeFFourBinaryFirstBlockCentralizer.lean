import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryFirstBlockEntry

/-! The selected prime-field entry is transported to the SAME original
fixed-group first ordered block. This excludes a nonzero isolated first
parameter from centralizing x, without a full twelve-bit formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryFirstBlockCentralizer
open CFSGReeFFourBinaryFirstOrderedBlock CFSGReeFFourBinaryFirstBlockEntry
open CFSGReeFFourMiddleDerivedFiveRootWords CFSGReeFFourOuterThreeWord
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGOpposedPeelingOrderedParameters CFSGReeFFourInversionPeelingWords
open CFSGFFourNormPrimeFieldWords CFSGFFourNormPrimeFieldVectorEvaluation

private theorem prime_evaluate_eq_of_wordValue_eq (K : Type) [_root_.Field K]
    [Finite K] [CharP K 2] (s t : List Letter)
    (h : wordValue K s=wordValue K t) (v : Fin 26 → ZMod 2) :
    evaluate (ZMod 2) s v=evaluate (ZMod 2) t v := by
  let e : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hk : evaluate K s (fun j => e (v j))=evaluate K t (fun j => e (v j)) := by
    rw [←wordValue_action K s (fun j => e (v j)),
      ←wordValue_action K t (fun j => e (v j)),h]
  funext j
  apply e.injective
  exact (congrFun (evaluate_map (ZMod 2) K e s v) j).trans
    ((congrFun hk j).trans (congrFun (evaluate_map (ZMod 2) K e t v) j).symm)

theorem first_ordered_commute_implies_zero (a : Fin 4)
    (h : Commute (orderedProduct (step 0 true) 8 (firstParameters a))
      (outerInvolution 0)) : a=0 := by
  have hy : wordValue (Field 0) (firstLetters a)=
      (orderedProduct (step 0 true) 8 (firstParameters a)).val :=
    (first_letters_value 0 a).trans
      (congrArg (fun g : originalModelFixed 0 => g.val) (first_ordered_value a)).symm
  have hx : wordValue (Field 0) outerLetters=(outerInvolution 0).val :=
    outerLetters_value 0
  have hw : wordValue (Field 0) (firstLetters a++outerLetters)=
      wordValue (Field 0) (outerLetters++firstLetters a) := by
    rw [wordValue_append,wordValue_append,hy,hx]
    exact congrArg (fun g : originalModelFixed 0 => g.val) h.eq
  exact evaluate_commute_implies_zero a
    (prime_evaluate_eq_of_wordValue_eq (Field 0) _ _ hw (coordinates (ZMod 2) initial))

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryFirstBlockCentralizer
