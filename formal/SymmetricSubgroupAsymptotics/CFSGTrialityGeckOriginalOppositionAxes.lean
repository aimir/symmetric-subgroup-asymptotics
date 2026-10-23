import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOppositionSignedGroups
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalNegativeRootIntersection
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! Literal relative opposition transports the SAME original opposed
pair in both directions and the intrinsic negative axes onto the full
positive fixed parameter axes. Its square is retained; no involution
or field-opposition identification is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOppositionAxes
open CFSGTrialityGeckOppositionSignedGroups CFSGTrialityGeckRelativeOpposition
open CFSGTrialityGeckOriginalNegativeRootIntersection CFSGTrialityGeckGeneratedPreimageCoordinates
open CFSGTrialityGeckGeneratedOriginalProjection CFSGTrialityGeckOriginalRootFamily
open CFSGTrialityGeckOriginalOppositeAlignment CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckRootGeneratedPGroup CFSGTrialityGeckNegativeParabolicRootIntersection
open CFSGTrialityGeckFixedOrbitRootGroups CFSGTrialityGeckNegativeOrbitRootGroups
open CFSGTrialityGeckOrbitZeroFunctionalGroup CFSGTrialityGeckSimpleOrbitFlags
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4NormTwo
open CFSGNormTwoCoordinateZeroFunctionalSupport CFSGSubgroupConjugateRestriction
open CFSGSerreOrdinaryTwists

private theorem subgroupOf_conjugation {G : Type*} [Group G]
    (J R S : Subgroup G) (hR : R≤J) (g : J)
    (he : R.map (MulAut.conj g.val).toMonoidHom=S) :
    (R.subgroupOf J).map (MulAut.conj g).toMonoidHom=S.subgroupOf J := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change g.val*y.val*g.val⁻¹∈S
    rw [←he]
    exact ⟨y.val,hy,rfl⟩
  · intro hx
    have hxS : x.val∈S := hx
    rw [←he] at hxS
    obtain ⟨y,hy,hyx⟩ := hxS
    exact ⟨⟨y,hR hy⟩,hy,Subtype.ext hyx⟩

def generatedOpposition (q : CFSG.PrimePower) :
    fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) :=
  ⟨relativeOpposition (q.Extension 3),relativeOpposition_mem_generated _ _⟩

def originalOpposition (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] : CFSG.Models.TrialityD4 q :=
  generatedToOriginal q (generatedOpposition q)

private theorem rootPart_opposition_map (q : CFSG.PrimePower) (neg : Bool) :
    (rootPart (q.Extension 3) (definingFieldAutomorphism q 3) neg).map
      (MulAut.conj (generatedOpposition q)).toMonoidHom=
        rootPart (q.Extension 3) (definingFieldAutomorphism q 3) (!neg) :=
  subgroupOf_conjugation _ _ _ (signedFixed_le_generated _ _ neg) (generatedOpposition q)
    (opposition_signedFixed_map _ _ neg)

theorem original_positive_opposition_map (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)).map
      (MulAut.conj (originalOpposition q)).toMonoidHom=originalNegative q := by
  have hh := congrArg (fun S : Subgroup
      (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3))=>
        S.map (generatedToOriginal q)) (rootPart_opposition_map q false)
  dsimp only at hh
  simp only [Bool.not_false,Bool.not_true] at hh
  rw [map_conjugate,rootPart_positive_original_image,rootPart_negative_original_image] at hh
  exact hh

theorem original_negative_opposition_map (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (originalNegative q).map (MulAut.conj (originalOpposition q)).toMonoidHom=
      (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)) := by
  have hh := congrArg (fun S : Subgroup
      (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3))=>
        S.map (generatedToOriginal q)) (rootPart_opposition_map q true)
  dsimp only at hh
  simp only [Bool.not_false,Bool.not_true] at hh
  rw [map_conjugate,rootPart_negative_original_image,rootPart_positive_original_image] at hh
  exact hh

def positiveOrbitRootGenerated (q : CFSG.PrimePower) (a : Bool) :
    Subgroup (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) :=
  (fixedOrbitRootGroup q a).subgroupOf
    (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3))

def originalPositiveOrbitRoot (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (a : Bool) :
    Subgroup (CFSG.Models.TrialityD4 q) :=
  (positiveOrbitRootGenerated q a).map (generatedToOriginal q)

private theorem negativeOrbitRootGenerated_opposition_map (q : CFSG.PrimePower) (a : Bool) :
    (negativeOrbitRootGenerated q a).map (MulAut.conj (generatedOpposition q)).toMonoidHom=
      positiveOrbitRootGenerated q a := by
  have hle : fixedOrbitNegative q a≤
      fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) := by
    rw [←fixed_negative_inf_simpleParabolic q a]
    exact inf_le_left.trans (signedFixed_le_generated _ _ true)
  exact subgroupOf_conjugation _ _ _ hle (generatedOpposition q)
    (opposition_fixedOrbit_negative_map q a)

theorem original_negative_axis_opposition_map (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (a : Bool) :
    (originalNegativeOrbitRoot q a).map (MulAut.conj (originalOpposition q)).toMonoidHom=
      originalPositiveOrbitRoot q a := by
  have hh := congrArg (fun S : Subgroup
      (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3))=>
        S.map (generatedToOriginal q)) (negativeOrbitRootGenerated_opposition_map q a)
  dsimp only at hh
  rw [map_conjugate] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOppositionAxes
