import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFiveCharacterIntervalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoCharacterIntervalRawEnvelope
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairQuotientPackage

/-!
# Character-interval four-pair rows

The four remaining large-kernel actions have one retained central axis.
Their quotient acts faithfully on at most six points, while every axis below
the centre has a one-slot socle generator certificate.  This file proves
the common counting and numerical theorem from exactly those structural
facts.  The finite action-row classifier is kept separate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Structural certificate for one of the Y2--Y5 four-pair actions.  The
socle-generator field is a literal normal-axis statement and contains no
counting or asymptotic estimate. -/
structure CertifiedFourPairCharacterModel
    (U : PreE7NonPairActionClass 8) : Type 1 where
  interval : SocleGeneratorCharacterIntervalData
    (preE7NonPairAction 8 U)
  quotientDegree_le_six : interval.quotientDegree ≤ 6
  slots_eq_one : interval.slots = 1

namespace CertifiedFourPairCharacterModel

variable {U : PreE7NonPairActionClass 8}
  (M : CertifiedFourPairCharacterModel U)

noncomputable def completeInterval
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    CompleteCharacterIntervalData (preE7NonPairAction 8 U) :=
  M.interval.toCompleteCharacterIntervalData hZmud

/-- Raw compressed complete-quotient envelope, retained for a later affine
layer.  Its comparator is the literal quotient by the certified axis. -/
noncomputable def quotientSummedEnvelope
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    PreE7DegreeTwoPairQuotientSummedEnvelope
      (preE7NonPairAction 8 U) :=
  (M.completeInterval hZmud).quotientSummedEnvelope lit

/-- The raw interval row with the literal faithful action of its quotient
comparator retained for affine-layer composition. -/
noncomputable def quotientSummedPackage
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    PreE7DegreeTwoPairQuotientSummedPackage
      (preE7NonPairAction 8 U) :=
  let D := M.completeInterval hZmud
  { envelope := D.quotientSummedEnvelope lit
    v := max 2 D.quotientDegree
    action := (characterComparatorPadHom (le_max_right 2 D.quotientDegree)).comp
      D.quotientAction
    action_injective :=
      (characterComparatorPadHom_injective
        (le_max_right 2 D.quotientDegree)).comp D.quotientAction_injective }

private theorem logb_two_five_lt_seven_thirds :
    Real.logb 2 5 < (7 : ℝ) / 3 := by
  have hp : (5 : ℝ) ^ (3 : ℕ) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (5 : ℝ) ^ (3 : ℕ)) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by
    simpa only [mul_comm] using hlog)

/-- The width-eight comparator and one-character tail both fit the global
pre-E7 window. -/
noncomputable def source
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 8 U := by
  let D := M.completeInterval hZmud
  apply PrimitiveAffineImprimitiveBlockTransfer.boundedCompleteCharacterSource
    D lit .tf
  · change preE7CharacterRho * (8 : ℕ) ≤
      ((evenWidth 8 : ℝ) -
        (max 2 M.interval.quotientDegree : ℕ)) / 8
    have hmax : max 2 M.interval.quotientDegree ≤ 6 :=
      max_le (by norm_num) M.quotientDegree_le_six
    have hmaxR : max (2 : ℝ) (M.interval.quotientDegree : ℝ) ≤ 6 := by
      exact_mod_cast hmax
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
    linarith
  · change (M.interval.slots : ℝ) * (Real.logb 2 5 / 3) ≤
      preE7CharacterWindow 8
    rw [M.slots_eq_one]
    norm_num only [Nat.cast_one, one_mul]
    have hlog := logb_two_five_lt_seven_thirds
    norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
    linarith
  · norm_num

end CertifiedFourPairCharacterModel
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
