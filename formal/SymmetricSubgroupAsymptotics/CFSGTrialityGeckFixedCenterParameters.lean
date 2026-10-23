import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveCenter
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedLongLine

/-! Literal fixed-field parameters of the full intrinsic fixed-U centre.
The actual highest-section parameterization is bijective; this does not
identify the whole fixed matrix group with an abstract triality group. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCenterParameters
open CFSGTrialityGeckFixedPositiveCenter CFSGTrialityGeckDerivedLongLine
open CFSGTrialityGeckFixedLongLine CFSGTrialityFixedField
open CFSGTrialityGeckShortCentralizerCardinality CFSGTrialityGeckSectionHeightMembership
open CFSGTrialityGeckSectionParameterRanges CFSGTrialityGeckSectionQuotientCoordinates
open CFSGTrialityGeckFixedRootSections CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckFixedPositiveGeneration
open CFSGTrialityGeckMatrixTwist CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGSerreOrdinaryTwists
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

def highestParameter (q : CFSG.PrimePower) (t : fixedField q) : highestLine q :=
  ⟨longPositiveFixed q t,by
    change fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3)
      (longPositiveFixed q t)∈RootLine (q.Extension 3) (longRoot 2)
    change (longPositiveSection (q.Extension 3) 2 (Multiplicative.ofAdd t.val)).val∈_
    rw [longPositiveSection_val]
    exact longSection_mem_root (q.Extension 3) 2 t.val⟩

theorem highestParameter_val (q : CFSG.PrimePower) (t : fixedField q) :
    fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3)
      (highestParameter q t).val=longSection (q.Extension 3) 2 false t.val :=
  longPositiveSection_val (q.Extension 3) 2 (Multiplicative.ofAdd t.val)

theorem highestParameter_bijective (q : CFSG.PrimePower) :
    Function.Bijective (highestParameter q) := by
  constructor
  · intro t s he
    have hh := congrArg (fun x : highestLine q=>
      fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3) x.val) he
    have hs := (highestParameter_val q t).symm.trans (hh.trans (highestParameter_val q s))
    apply Subtype.ext
    exact (longParameter_bijective (q.Extension 3) 2).1 (Subtype.ext hs)
  · intro u
    obtain ⟨t,ht⟩ := longParameter_surjective (q.Extension 3) 2
      ⟨fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3) u.val,u.property⟩
    have he : longSection (q.Extension 3) 2 false t=
        fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3) u.val :=
      congrArg Subtype.val ht
    have huf : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
        (fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3) u.val)=
      fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3) u.val := by
      have hh := congrArg (fun z : Positive (q.Extension 3)=>z.val) u.val.property
      change (positiveTwist (q.Extension 3) (definingFieldAutomorphism q 3) u.val.val).val=
        u.val.val.val at hh
      rw [positiveTwist_val] at hh
      exact hh
    have hts : longSection (q.Extension 3) 2 false (definingFieldAutomorphism q 3 t)=
        longSection (q.Extension 3) 2 false t :=
      (highest_long_twist q t).symm.trans
        ((congrArg (unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)) he).trans
          (huf.trans he.symm))
    have htf : definingFieldAutomorphism q 3 t=t :=
      (longParameter_bijective (q.Extension 3) 2).1 (Subtype.ext hts)
    refine ⟨⟨t,htf⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact (highestParameter_val q ⟨t,htf⟩).trans he

theorem fixedPositive_center_card (q : CFSG.PrimePower) :
    Nat.card (Subgroup.center (fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3)))=
      q.order := by
  rw [Nat.card_congr (MulEquiv.subgroupCongr (center_eq_highestLine q)).toEquiv]
  exact (Nat.card_congr (Equiv.ofBijective (highestParameter q)
    (highestParameter_bijective q))).symm.trans (fixedField_card q)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCenterParameters
