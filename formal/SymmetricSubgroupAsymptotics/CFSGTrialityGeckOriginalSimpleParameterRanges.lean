import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSignedRootAction
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleChartWeyl

/-! Exact ranges of the four additive homomorphisms in the SAME original
triality group. The negative charts are transported through the proved
literal fixed simple Weyl word; no separate fixed-class lifting premise
or abstract root-group identification is supplied. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSimpleParameterRanges
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckOriginalSimpleParameters CFSGTrialityGeckSignedSimpleParameters
open CFSGTrialityGeckFixedOrbitRootGroups CFSGTrialityGeckNegativeOrbitRootGroups
open CFSGTrialityGeckNegativeParabolicRootIntersection CFSGTrialityGeckOriginalNegativeRootIntersection
open CFSGTrialityGeckOriginalOppositionAxes CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortOrbitCommutator
open CFSGTrialityGeckSimpleChartWeyl CFSGTrialityGeckSimpleOrbitFlags
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityFixedField
open CFSGSerreQuadraticWeylWord CFSGSerreOrdinaryTwists
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

private theorem codRestrict_range {A G : Type*} [Group A] [Group G]
    (f : A→*G) (H : Subgroup G) (hf : ∀x,f x∈H) :
    (f.codRestrict H hf).range=f.range.subgroupOf H := by
  ext g
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩
  · rintro ⟨t,ht⟩
    exact ⟨t,Subtype.ext ht⟩

private theorem range_map_neg {A G : Type*} [AddGroup A] [Group G]
    (x y : Multiplicative A→*G) (e : MulAut G)
    (he : ∀t:A,e (x (Multiplicative.ofAdd t))=y (Multiplicative.ofAdd (-t))) :
    x.range.map e.toMonoidHom=y.range := by
  ext g
  constructor
  · rintro ⟨_,⟨t,rfl⟩,rfl⟩
    exact ⟨Multiplicative.ofAdd (-t.toAdd),(he t.toAdd).symm⟩
  · rintro ⟨t,rfl⟩
    refine ⟨x (Multiplicative.ofAdd (-t.toAdd)),⟨Multiplicative.ofAdd (-t.toAdd),rfl⟩,?_⟩
    simpa only [neg_neg] using he (-t.toAdd)

theorem shortRawHom_range (q : CFSG.PrimePower) (neg : Bool) :
    (shortOrbitHom (q.Extension 3) (definingFieldAutomorphism q 3) neg).range=
      if neg then fixedOrbitNegative q false else fixedOrbitRootGroup q false := by
  have hpos : (shortOrbitHom (q.Extension 3) (definingFieldAutomorphism q 3) false).range=
      fixedOrbitRootGroup q false := by
    ext g
    constructor
    · rintro ⟨t,rfl⟩
      exact (shortFixedParameter q t.toAdd).property
    · intro hg
      obtain ⟨t,ht⟩ := (shortFixedParameter_bijective q).2 ⟨g,hg⟩
      exact ⟨Multiplicative.ofAdd t,congrArg Subtype.val ht⟩
  cases neg
  · exact hpos
  · have hm := range_map_neg
      (shortOrbitHom (q.Extension 3) (definingFieldAutomorphism q 3) false)
      (shortOrbitHom (q.Extension 3) (definingFieldAutomorphism q 3) true)
      (MulAut.conj (canonicalWord rawData (q.Extension 3) (orbitWord false)))
      (short_word_conjugates _ _)
    rw [hpos,fixedOrbitRootGroup_map] at hm
    exact hm.symm

theorem middleRawHom_range (q : CFSG.PrimePower) (neg : Bool) :
    (middleRawHom q neg).range=
      if neg then fixedOrbitNegative q true else fixedOrbitRootGroup q true := by
  have hpos : (middleRawHom q false).range=fixedOrbitRootGroup q true := by
    ext g
    constructor
    · rintro ⟨t,rfl⟩
      exact (middleFixedParameter q t.toAdd).property
    · intro hg
      obtain ⟨t,ht⟩ := (middleFixedParameter_bijective q).2 ⟨g,hg⟩
      exact ⟨Multiplicative.ofAdd t,congrArg Subtype.val ht⟩
  cases neg
  · exact hpos
  · have hm := range_map_neg (middleRawHom q false) (middleRawHom q true)
      (MulAut.conj (canonicalWord rawData (q.Extension 3) (orbitWord true)))
      (fun t:fixedField q=>middle_word_conjugates (q.Extension 3) t.val)
    rw [hpos,fixedOrbitRootGroup_map] at hm
    exact hm.symm

theorem shortGeneratedHom_range (q : CFSG.PrimePower) (neg : Bool) :
    (shortGeneratedHom q neg).range=
      if neg then negativeOrbitRootGenerated q false else positiveOrbitRootGenerated q false := by
  rw [shortGeneratedHom,codRestrict_range,shortRawHom_range]
  cases neg <;> rfl

theorem middleGeneratedHom_range (q : CFSG.PrimePower) (neg : Bool) :
    (middleGeneratedHom q neg).range=
      if neg then negativeOrbitRootGenerated q true else positiveOrbitRootGenerated q true := by
  rw [middleGeneratedHom,codRestrict_range,middleRawHom_range]
  cases neg <;> rfl

theorem originalShortHom_range (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (neg : Bool) :
    (originalShortHom q neg).range=
      if neg then originalNegativeOrbitRoot q false else originalPositiveOrbitRoot q false := by
  rw [originalShortHom,MonoidHom.range_comp,shortGeneratedHom_range]
  cases neg <;> rfl

theorem originalMiddleHom_range (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (neg : Bool) :
    (originalMiddleHom q neg).range=
      if neg then originalNegativeOrbitRoot q true else originalPositiveOrbitRoot q true := by
  rw [originalMiddleHom,MonoidHom.range_comp,middleGeneratedHom_range]
  cases neg <;> rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSimpleParameterRanges
