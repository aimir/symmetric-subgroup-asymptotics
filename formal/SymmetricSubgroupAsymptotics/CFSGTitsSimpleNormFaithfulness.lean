import SymmetricSubgroupAsymptotics.CFSGTitsDerivedCentralQuotientEquivalence
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedOuterMatrix
import SymmetricSubgroupAsymptotics.CFSGFFourNormSparseWordMatrix
import Mathlib.GroupTheory.Subgroup.Simple

/-! Conditional faithfulness of the genuine norm representation on the
original binary derived group.  Simplicity is retained explicitly as
the already-existing simple-model hypothesis.  The actual full-centre
quotient equivalence and one nonzero outer-root matrix entry discharge
the kernel argument; no norm-faithfulness premise is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTitsSimpleNormFaithfulness
open CFSGTitsDerivedCentralQuotientEquivalence
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGFFourNormCertificateAction CFSGFFourOriginalFoldedEquivalence
open CFSGFFourNormPrimeFieldWords CFSGFFourNormSparseWordMatrix
open CFSGReeFFourMiddleDerivedFiveRootWords CFSGReeFFourBinarySeedOuterMatrix
open CFSGReeFFourBinaryOuterSaving CFSGReeFFourOuterThreeWord

private abbrev D := commutator (originalModelFixed 0)

def sourceAction : D →* Module.End (Field 0) (Fin 26 → Field 0) :=
  (linearAction (Field 0)).comp ((modelEquivFolded (Field 0)).toMonoidHom.comp
    ((originalModelFixed 0).subtype.comp D.subtype))

theorem sourceAction_word (d : D) (s : List Letter)
    (h : ((d : originalModelFixed 0) : CFSG.Models.Chevalley.Model CartanMatrix.F₄ (Field 0))=
      wordValue (Field 0) s) (v : Fin 26 → Field 0) :
    sourceAction d v=evaluate (Field 0) s v := by
  change linearAction (Field 0) (modelEquivFolded (Field 0)
    ((d : originalModelFixed 0) : CFSG.Models.Chevalley.Model CartanMatrix.F₄ (Field 0))) v=_
  rw [h]
  exact wordValue_action (Field 0) s v

theorem sourceAction_outer_ne_one :
    sourceAction ⟨outerInvolution 0,outer_mem_derived 0⟩≠1 := by
  intro h
  let e : ZMod 2 →+* Field 0 := ZMod.castHom (dvd_refl 2) (Field 0)
  let v : Fin 26 → ZMod 2 := fun j => if j=10 then 1 else 0
  have heval : evaluate (ZMod 2) outerLetters v 0=1 := by
    exact outer_matrix_entry 0 10
  have hmap := congrFun (evaluate_map (ZMod 2) (Field 0) e outerLetters v) 0
  have hword : sourceAction ⟨outerInvolution 0,outer_mem_derived 0⟩
      (fun j => e (v j))=evaluate (Field 0) outerLetters (fun j => e (v j)) :=
    sourceAction_word _ outerLetters (outerLetters_value 0).symm _
  have hzero : evaluate (Field 0) outerLetters (fun j => e (v j)) 0=0 := by
    rw [←hword,h]
    change e (v 0)=0
    change e (if (0 : Fin 26)=10 then 1 else 0)=0
    rw [if_neg (by decide),map_zero]
  rw [heval,map_one,hzero] at hmap
  exact one_ne_zero hmap

theorem sourceAction_injective [IsSimpleGroup CFSG.Models.Tits] :
    Function.Injective sourceAction := by
  letI : IsSimpleGroup D := derivedEquivTits.isSimpleGroup
  apply sourceAction.ker_eq_bot_iff.mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal sourceAction.ker inferInstance with hb|ht
  · exact hb
  · have hx : (⟨outerInvolution 0,outer_mem_derived 0⟩ : D)∈sourceAction.ker := by
      rw [ht]
      exact Subgroup.mem_top _
    exact False.elim (sourceAction_outer_ne_one hx)

theorem wordMatrix_map (s : List Letter) :
    (wordMatrix (ZMod 2) s).map (ZMod.castHom (dvd_refl 2) (Field 0))=
      wordMatrix (Field 0) s := by
  let e : ZMod 2 →+* Field 0 := ZMod.castHom (dvd_refl 2) (Field 0)
  ext i j
  have h := congrFun (evaluate_map (ZMod 2) (Field 0) e s
    (fun k : Fin 26 => if k=j then 1 else 0)) i
  simpa only [evaluate_basis_entry,apply_ite,map_one,map_zero] using h

theorem eq_of_primeField_wordMatrix_eq [IsSimpleGroup CFSG.Models.Tits]
    (d e : D) (s t : List Letter)
    (hd : ((d : originalModelFixed 0) : CFSG.Models.Chevalley.Model CartanMatrix.F₄ (Field 0))=
      wordValue (Field 0) s)
    (he : ((e : originalModelFixed 0) : CFSG.Models.Chevalley.Model CartanMatrix.F₄ (Field 0))=
      wordValue (Field 0) t)
    (hM : wordMatrix (ZMod 2) s=wordMatrix (ZMod 2) t) : d=e := by
  apply sourceAction_injective
  have hK : wordMatrix (Field 0) s=wordMatrix (Field 0) t := by
    rw [←wordMatrix_map s,←wordMatrix_map t,hM]
  apply LinearMap.ext
  intro v
  funext i
  change sourceAction d v i=sourceAction e v i
  rw [sourceAction_word d s hd,sourceAction_word e t he,
    evaluate_eq_mulVec,evaluate_eq_mulVec,hK]

end SymmetricSubgroupAsymptotics.CFSGTitsSimpleNormFaithfulness
