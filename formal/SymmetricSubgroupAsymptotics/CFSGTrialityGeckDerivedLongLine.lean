import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedLongLine
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveImageSylow

/-! The genuine fixed highest-root line embeds into the SAME derived
image, has q members, and lies in the already proved actual positive Sylow. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedLongLine
open CFSGTrialityGeckFixedLongLine CFSGTrialityFixedField
open CFSGTrialityGeckFixedDerivedMatrixLift CFSGTrialityGeckFixedPositiveImageSylow
open CFSGTrialityGeckDerivedSylowNormalizer CFSGTrialityGeckSourceWordAction
open CFSGTrialityGeckLongDerivedImage CFSGTrialityGeckFixedPositiveGeneration
open CFSGTrialityGeckSectionQuotientCoordinates CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckSectionParameterRanges CFSGTrialityGeckPositiveActionInjective
open CFSGSerreOrdinaryTwists

local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) :=
  Classical.decEq _

def longToDerived (q : CFSG.PrimePower) : fixedLongLine q →* DerivedImage q :=
  ((fixedMatrixAction q).comp (fixedLongLine q).subtype).codRestrict _
    (fun x => fixedLongLine_action_le_derived q ⟨x.val,x.property,rfl⟩)

theorem longToDerived_val (q : CFSG.PrimePower) (x : fixedLongLine q) :
    (longToDerived q x).val = fixedMatrixAction q x.val := rfl

def longPositiveFixed (q : CFSG.PrimePower) (t : fixedField q) :
    fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3) :=
  ⟨longPositiveSection (q.Extension 3) 2 (Multiplicative.ofAdd t.val),
    longPositiveSection_fixed (q.Extension 3) (definingFieldAutomorphism q 3) 2
      (Multiplicative.ofAdd t.val) t.property⟩

theorem parameter_action_eq_positive (q : CFSG.PrimePower) (t : fixedField q) :
    fixedMatrixAction q (fixedLongParameter q t).val =
      positiveAction (q.Extension 3) (longPositiveFixed q t).val := by
  change matrixAction (q.Extension 3)
      (CFSGTrialityGeckOriginalFixedSections.matrixLongSection (q.Extension 3) 2 false t.val) =
    matrixAction (q.Extension 3) (positiveInclusion (q.Extension 3)
      (longPositiveSection (q.Extension 3) 2 (Multiplicative.ofAdd t.val)))
  apply congrArg (matrixAction (q.Extension 3))
  apply Subtype.ext
  rw [CFSGTrialityGeckOriginalFixedSections.matrixLongSection_val,
    positiveInclusion_val,longPositiveSection_val]
  rfl

private theorem mem_of_subgroup_eq {G : Type*} [Group G] (P Q : Subgroup G)
    (h : P = Q) (x : G) (hx : x ∈ Q) : x ∈ P := h.symm ▸ hx

theorem longToDerived_mem_positiveSylow (q : CFSG.PrimePower) (x : fixedLongLine q) :
    longToDerived q x ∈ imagePositiveSylow q := by
  obtain ⟨t,rfl⟩ := fixedLongParameter_surjective q x
  let u := longPositiveFixed q t
  let v := (preimagePositiveEquiv q).symm u
  change longToDerived q (fixedLongParameter q t) ∈
    (imagePositiveSylow q : Subgroup (DerivedImage q))
  have he : preimageToImage q v.val = longToDerived q (fixedLongParameter q t) := by
    apply Subtype.ext
    calc
      (preimageToImage q v.val).val =
          positiveAction (q.Extension 3) (preimagePositiveEquiv q v).val :=
        preimagePositiveEquiv_action q v
      _ = positiveAction (q.Extension 3) u.val :=
        congrArg (fun z : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3) =>
          positiveAction (q.Extension 3) z.val) ((preimagePositiveEquiv q).apply_symm_apply u)
      _ = fixedMatrixAction q (fixedLongParameter q t).val := (parameter_action_eq_positive q t).symm
      _ = (longToDerived q (fixedLongParameter q t)).val := rfl
  have hm : longToDerived q (fixedLongParameter q t) ∈
      ((preimageToImage q).comp
        (preimageSylow q : Subgroup (naturalDerivedPreimage q)).subtype).range := ⟨v,he⟩
  exact mem_of_subgroup_eq _ _ (imagePositiveSylow_range q) _ hm

theorem longToDerived_injective (q : CFSG.PrimePower) : Function.Injective (longToDerived q) := by
  intro x y he
  obtain ⟨t,rfl⟩ := fixedLongParameter_surjective q x
  obtain ⟨u,rfl⟩ := fixedLongParameter_surjective q y
  have ha := congrArg (fun z : DerivedImage q => z.val) he
  have hp : positiveAction (q.Extension 3) (longPositiveFixed q t).val =
      positiveAction (q.Extension 3) (longPositiveFixed q u).val :=
    (parameter_action_eq_positive q t).symm.trans (ha.trans (parameter_action_eq_positive q u))
  have hv := positiveAction_injective (q.Extension 3) q.prime hp
  have hr := congrArg (fun z : Positive (q.Extension 3) => z.val) hv
  have hs : CFSGTrialityGeckFixedRootSections.longSection (q.Extension 3) 2 false t.val =
      CFSGTrialityGeckFixedRootSections.longSection (q.Extension 3) 2 false u.val :=
    (longPositiveSection_val (q.Extension 3) 2 (Multiplicative.ofAdd t.val)).symm.trans
      (hr.trans (longPositiveSection_val (q.Extension 3) 2 (Multiplicative.ofAdd u.val)))
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact (fixedLongParameter_val q t).trans (hs.trans (fixedLongParameter_val q u).symm)

def derivedLongLine (q : CFSG.PrimePower) : Subgroup (DerivedImage q) :=
  (longToDerived q).range

theorem derivedLongLine_le_positiveSylow (q : CFSG.PrimePower) :
    derivedLongLine q ≤ (imagePositiveSylow q : Subgroup (DerivedImage q)) := by
  rintro _ ⟨x,rfl⟩
  exact longToDerived_mem_positiveSylow q x

theorem derivedLongLine_card (q : CFSG.PrimePower) : Nat.card (derivedLongLine q) = q.order :=
  (Nat.card_congr (MonoidHom.ofInjective (longToDerived_injective q)).toEquiv).symm.trans
    (fixedLongLine_card q)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedLongLine
