import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightCertificateField
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterFixedRoot
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeSimpleWeyl
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum

/-! The selected two-block word is an element of the literal original
fixed group. The finite-field identification is an actual ring equivalence;
no action certificate or model recognition is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightFixedSelectedWord
open CFSGReeFFourFieldEightCertificateField CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourMiddleFixedWords CFSGReeFFourOuterFixedRoot
open CFSGReeFFourRelativeSimpleWeyl

private instance : Fintype (Field 1) := Fintype.ofFinite _

def fieldEquiv : Element ≃+* Field 1 :=
  FiniteField.ringEquivOfCardEq (by
    have hcard : Nat.card Element = Nat.card (Field 1) := by
      rw [card, field_card]
      norm_num
    simpa only [Nat.card_eq_fintype_card] using hcard)

def selectedBlock (a b c : Element) : originalModelFixed 1 :=
  ⟨outerWord 1 (fieldEquiv a) * fixedMiddleWord 1 (fieldEquiv b) (fieldEquiv c) *
    outerRelativeWeyl 1 * middleRelativeWeyl 1, by
      change reeAutomorphism 1 (outerWord 1 (fieldEquiv a) *
        fixedMiddleWord 1 (fieldEquiv b) (fieldEquiv c) *
        outerRelativeWeyl 1 * middleRelativeWeyl 1) = _
      simp only [map_mul, outerWord_fixed, fixedMiddleWord_fixed,
        outerRelativeWeyl_fixed, middleRelativeWeyl_fixed]⟩

theorem selectedBlock_val (a b c : Element) :
    (selectedBlock a b c).val =
      outerWord 1 (fieldEquiv a) * fixedMiddleWord 1 (fieldEquiv b) (fieldEquiv c) *
        outerRelativeWeyl 1 * middleRelativeWeyl 1 := rfl

def selectedElement : originalModelFixed 1 :=
  selectedBlock (ofBits 1) (ofBits 4) (ofBits 3) *
    selectedBlock (ofBits 7) (ofBits 1) (ofBits 0)

theorem selectedElement_val : selectedElement.val =
    (selectedBlock (ofBits 1) (ofBits 4) (ofBits 3)).val *
      (selectedBlock (ofBits 7) (ofBits 1) (ofBits 0)).val := rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightFixedSelectedWord
