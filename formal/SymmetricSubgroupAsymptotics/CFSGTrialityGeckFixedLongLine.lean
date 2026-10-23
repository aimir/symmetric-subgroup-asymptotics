import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedDerivedMatrixLift
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionParameterRanges
import SymmetricSubgroupAsymptotics.CFSGTrialityFixedField

/-! The exact highest long line inside the genuine fixed matrix group
has the literal fixed-field parameters, and its actual action belongs
to the SAME original derived action image. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedLongLine
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityGeckSectionHeightMembership
open CFSGTrialityGeckFixedDerivedMatrixLift CFSGTrialityGeckMatrixGroupTwist
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckLongDerivedImage
open CFSGTrialityGeckOriginalFixedSections CFSGTrialityGeckFixedRootSections
open CFSGTrialityGeckSectionParameterRanges CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckRootSubgroupTwist
open CFSGTrialityFixedField CFSGSerreOrdinaryTwists

local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) :=
  Classical.decEq _

def fixedRawInclusion (q : CFSG.PrimePower) :
    FixedMatrixGroup q →* (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ :=
  (MatrixGroup (q.Extension 3)).subtype.comp (FixedMatrixGroup q).subtype

def fixedLongLine (q : CFSG.PrimePower) : Subgroup (FixedMatrixGroup q) :=
  (RootLine (q.Extension 3) (longRoot 2)).comap (fixedRawInclusion q)

theorem highest_long_twist (q : CFSG.PrimePower) (t : q.Extension 3) :
    unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (longSection (q.Extension 3) 2 false t) =
    longSection (q.Extension 3) 2 false (definingFieldAutomorphism q 3 t) := by
  simp only [longSection,map_mul,map_inv,longTransport_fixed,unitTwist_raw_root]
  rfl

def fixedLongParameter (q : CFSG.PrimePower) (t : fixedField q) : fixedLongLine q := by
  refine ⟨⟨matrixLongSection (q.Extension 3) 2 false t.val, ?_⟩, ?_⟩
  · change matrixGroupTwist (q.Extension 3) (definingFieldAutomorphism q 3)
        (matrixLongSection (q.Extension 3) 2 false t.val) =
      matrixLongSection (q.Extension 3) 2 false t.val
    apply Subtype.ext
    rw [matrixGroupTwist_val,matrixLongSection_val]
    exact longSection_fixed (q.Extension 3) (definingFieldAutomorphism q 3) 2 false t.val t.property
  · change (matrixLongSection (q.Extension 3) 2 false t.val).val ∈
      RootLine (q.Extension 3) (longRoot 2)
    rw [matrixLongSection_val]
    exact longSection_mem_root (q.Extension 3) 2 t.val

theorem fixedLongParameter_val (q : CFSG.PrimePower) (t : fixedField q) :
    fixedRawInclusion q (fixedLongParameter q t).val =
      longSection (q.Extension 3) 2 false t.val :=
  matrixLongSection_val (q.Extension 3) 2 false t.val

theorem fixedLongParameter_injective (q : CFSG.PrimePower) :
    Function.Injective (fixedLongParameter q) := by
  intro t u he
  have hh := congrArg (fun x : fixedLongLine q => fixedRawInclusion q x.val) he
  have hs := (fixedLongParameter_val q t).symm.trans (hh.trans (fixedLongParameter_val q u))
  apply Subtype.ext
  apply (longParameter_bijective (q.Extension 3) 2).1
  exact Subtype.ext hs

theorem fixedLongParameter_surjective (q : CFSG.PrimePower) :
    Function.Surjective (fixedLongParameter q) := by
  intro x
  obtain ⟨t,ht⟩ := longParameter_surjective (q.Extension 3) 2
    ⟨fixedRawInclusion q x.val,x.property⟩
  have he : longSection (q.Extension 3) 2 false t = fixedRawInclusion q x.val :=
    congrArg Subtype.val ht
  have hxf : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (fixedRawInclusion q x.val) = fixedRawInclusion q x.val := by
    have h := congrArg (fun z : MatrixGroup (q.Extension 3) => z.val) x.val.property
    exact (matrixGroupTwist_val (q.Extension 3) (definingFieldAutomorphism q 3) x.val.val).symm.trans h
  have hs : longSection (q.Extension 3) 2 false (definingFieldAutomorphism q 3 t) =
      longSection (q.Extension 3) 2 false t :=
    (highest_long_twist q t).symm.trans
      ((congrArg (unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)) he).trans
        (hxf.trans he.symm))
  have htf : definingFieldAutomorphism q 3 t = t := by
    apply (longParameter_bijective (q.Extension 3) 2).1
    exact Subtype.ext hs
  refine ⟨⟨t,htf⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact (fixedLongParameter_val q ⟨t,htf⟩).trans he

theorem fixedLongLine_card (q : CFSG.PrimePower) : Nat.card (fixedLongLine q) = q.order :=
  (Nat.card_congr (Equiv.ofBijective (fixedLongParameter q)
    ⟨fixedLongParameter_injective q,fixedLongParameter_surjective q⟩)).symm.trans (fixedField_card q)

theorem fixedLongLine_action_le_derived (q : CFSG.PrimePower) :
    (fixedLongLine q).map (fixedMatrixAction q) ≤ (derivedImageAction q).range := by
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨t,ht⟩ := fixedLongParameter_surjective q ⟨x,hx⟩
  have he : x = (fixedLongParameter q t).val := congrArg Subtype.val ht.symm
  rw [he]
  change matrixAction (q.Extension 3) (matrixLongSection (q.Extension 3) 2 false t.val) ∈
    (derivedImageAction q).range
  have hm := long_source_action_mem_derived q 2 t.val t.property
  rw [sourceLongSection_action] at hm
  exact hm

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedLongLine
