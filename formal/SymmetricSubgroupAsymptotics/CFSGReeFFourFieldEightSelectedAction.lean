import SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateAction
import SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparseWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightWordEvaluation

/-! The actual original fixed-source action evaluates the selected
endomorphism word. Its fixed-group and field identifications are literal;
no equality is inferred from a separate recognized group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightSelectedAction
open CFSGFFourNormCertificateAction CFSGFFourNormCertificateSparseWords
open CFSGReeFFourFieldEightWordEvaluation CFSGReeFFourFieldEightWordTemplates
open CFSGReeFFourFieldEightFixedSelectedWord CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGFFourOriginalFoldedEquivalence
open CFSGSerreModelRootGeneration CFSGFFourE6CharacteristicTwoNormImage
private instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

def fixedLinearAction : originalModelFixed 1 →* Module.End (Field 1) (Fin 26 → Field 1) :=
  (linearAction (Field 1)).comp
    ((modelEquivFolded (Field 1)).toMonoidHom.comp (originalModelFixed 1).subtype)

def fixedVectorAction : originalModelFixed 1 →* Function.End (Fin 26 → Field 1) :=
  (vectorAction (Field 1)).comp
    ((modelEquivFolded (Field 1)).toMonoidHom.comp (originalModelFixed 1).subtype)

private theorem wordValue_cons (x : Letter) (s : List Letter) :
    wordValue (x::s) = modelRoot CartanMatrix.F₄ (Field 1) x.1 x.2.1
      (fieldEquiv x.2.2) * wordValue s := rfl

theorem wordValue_action (s : List Letter) :
    linearAction (Field 1) (modelEquivFolded (Field 1) (wordValue s)) =
      wordEnd (Field 1) fieldEquiv.toRingHom s := by
  induction s with
  | nil =>
    change linearAction (Field 1) (modelEquivFolded (Field 1) 1) = 1
    rw [map_one, map_one]
  | cons x s ih =>
    apply LinearMap.ext
    intro v
    rw [wordValue_cons, map_mul, map_mul, modelEquivFolded_root,
      Module.End.mul_apply, wordEnd_cons_apply]
    change linearAction (Field 1) (foldedRoot (Field 1) x.1 x.2.1 (fieldEquiv x.2.2))
      (linearAction (Field 1) (modelEquivFolded (Field 1) (wordValue s)) v) = _
    rw [linearAction_root_apply, ih]
    rfl

theorem selectedElement_action :
    fixedLinearAction selectedElement = wordEnd (Field 1) fieldEquiv.toRingHom selectedLetters := by
  change linearAction (Field 1) (modelEquivFolded (Field 1) selectedElement.val) = _
  rw [← selectedLetters_value]
  exact wordValue_action selectedLetters

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightSelectedAction
