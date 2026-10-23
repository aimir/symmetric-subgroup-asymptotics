import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveDerivedEquiv
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCenterParameters
import SymmetricSubgroupAsymptotics.CFSGInjectiveCenterImage

/-! The intrinsic centre of the actual positive Sylow, viewed in the
SAME original derived image, is precisely the previously counted
highest long root subgroup. No automorphism lifting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedCenterImage
open CFSGTrialityGeckPositiveDerivedEquiv CFSGTrialityGeckFixedCenterParameters
open CFSGTrialityGeckFixedPositiveCenter CFSGTrialityGeckDerivedLongLine
open CFSGTrialityGeckFixedLongLine CFSGTrialityFixedField
open CFSGTrialityGeckFixedPositiveImageSylow CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckFixedPositiveGeneration CFSGSerreOrdinaryTwists
open CFSGTrialityGeckFixedDerivedMatrixLift CFSGTrialityGeckSourceWordAction

theorem positive_highest_action (q : CFSG.PrimePower) (t : fixedField q) :
    positiveToDerived q (longPositiveFixed q t)=longToDerived q (fixedLongParameter q t) := by
  apply Subtype.ext
  calc
    (positiveToDerived q (longPositiveFixed q t)).val=
        positiveAction (q.Extension 3) (longPositiveFixed q t).val :=
      positiveEquivSylow_action q (longPositiveFixed q t)
    _=fixedMatrixAction q (fixedLongParameter q t).val :=
      (parameter_action_eq_positive q t).symm
    _=(longToDerived q (fixedLongParameter q t)).val := rfl

private theorem map_eq_range_of_parameters {G H B A : Type*} [Group G] [Group H] [Group B]
    (f : G→*H) (C : Subgroup G) (p : A→C) (hp : Function.Surjective p)
    (g : B→*H) (r : A→B) (hr : Function.Surjective r)
    (h : ∀a, f (p a).val=g (r a)) : C.map f=g.range := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨a,ha⟩ := hp ⟨z,hz⟩
    have hv : (p a).val=z := congrArg Subtype.val ha
    exact ⟨r a,(h a).symm.trans (congrArg f hv)⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨a,ha⟩ := hr z
    exact ⟨(p a).val,(p a).property,(h a).trans (congrArg g ha)⟩

theorem positive_center_image (q : CFSG.PrimePower) :
    (Subgroup.center (fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3))).map
      (positiveToDerived q)=derivedLongLine q := by
  rw [center_eq_highestLine]
  exact map_eq_range_of_parameters (positiveToDerived q) (highestLine q)
    (highestParameter q) (highestParameter_bijective q).2
    (longToDerived q) (fixedLongParameter q) (fixedLongParameter_surjective q)
    (positive_highest_action q)

theorem sylow_center_image (q : CFSG.PrimePower) :
    (Subgroup.center (imagePositiveSylow q)).map
      (imagePositiveSylow q : Subgroup (DerivedImage q)).subtype=derivedLongLine q := by
  have he := CFSGInjectiveCenterImage.center_image (positiveToDerived q)
    (positiveToDerived_injective q)
  rw [positiveToDerived_range,positive_center_image] at he
  exact he.symm

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedCenterImage
