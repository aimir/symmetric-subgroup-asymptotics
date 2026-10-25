import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryNormalizerParabolicCover
import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveCardLower

/-! The literal U intersection D, viewed in the same full fixed group,
satisfies every premise of the binary normalizer cover. Its normalizer
therefore lies in one actual minimal parabolic. This is not yet a claim
about solubility or the normalizer after the full derived-centre quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedNormalizerParabolic
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourDerivedPositiveCardLower
open CFSGReeFFourBinaryNormalizerParabolicCover
open CFSGReeFFourOuterParabolicFlag CFSGReeFFourMiddleParabolicFlag

def ambientDerivedPositive (m : ℕ) : Subgroup (originalModelFixed m) :=
  fixedPositive m ⊓ commutator (originalModelFixed m)

def derivedPositiveEquivAmbient (m : ℕ) : derivedPositive m ≃* ambientDerivedPositive m where
  toFun x := ⟨x.val.val, ⟨x.property, x.val.property⟩⟩
  invFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem ambientDerivedPositive_zero_card_lower :
    512 ≤ Nat.card (ambientDerivedPositive 0) :=
  tits_positive_card_lower.trans_eq (Nat.card_congr (derivedPositiveEquivAmbient 0).toEquiv)

theorem fixedPositive_le_normalizer_ambientDerivedPositive (m : ℕ) :
    fixedPositive m ≤ Subgroup.normalizer (ambientDerivedPositive m : Set (originalModelFixed m)) := by
  intro g hg
  have hU : g ∈ Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m)) :=
    (fixedPositive m).le_normalizer hg
  have hD : g ∈ Subgroup.normalizer
      (commutator (originalModelFixed m) : Set (originalModelFixed m)) :=
    Subgroup.le_normalizer_of_normal hg
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hU, hD⟩

theorem ambientDerivedPositive_zero_normalizer_le_outer_or_middle :
    Subgroup.normalizer (ambientDerivedPositive 0 : Set (originalModelFixed 0)) ≤ outerParabolic 0 ∨
      Subgroup.normalizer (ambientDerivedPositive 0 : Set (originalModelFixed 0)) ≤ middleParabolic 0 :=
  normalizer_le_outer_or_middle (ambientDerivedPositive 0) inf_le_left
    ambientDerivedPositive_zero_card_lower (fixedPositive_le_normalizer_ambientDerivedPositive 0)

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryDerivedNormalizerParabolic
