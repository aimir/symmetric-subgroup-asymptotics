import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryDerivedCover
import SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalDerivedGeneration

/-! The literal dimension-three fixed matrices cover the original
derived source when q >= 3.  This uses the proved rank-two root-word
generation, retaining the original central quotient throughout. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists CFSGSerreFixedRootElements

theorem rankTwoFixed_mem_derived (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (g : naturalFixed 2 q) :
    naturalFixedToOriginal q 2 g ∈ commutator (Fixed 2 q) := by
  obtain ⟨t, ht0, htc⟩ := CFSGTwistedAUnitaryNaturalRadical.exists_nonzero_central_parameter q 0
  have ht : t ^ q.order = -t := by
    change definingFieldAutomorphism q 2 t = -t
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [CFSGTwistedAUnitaryNaturalRadical.parity, pow_zero, one_mul] using
      (CFSGTwistedAUnitaryNaturalRadical.centralCondition_iff q 0 t).mp htc
  have hn := CFSGTwistedA2UnipotentArrays.isometric_mem_rootGenerated q t ht0 ht g.val
    (fixed_unit_isometric (q.Extension 2) 2 (definingFieldAutomorphism q 2).toRingHom
      g.val.val g.property)
  have hm := CFSGTwistedA2UnipotentArrays.naturalRootGenerated_map_le_original q t ht
    ⟨g.val, hn, rfl⟩
  obtain ⟨x, hx, he⟩ := hm
  have hxg : x = naturalFixedToOriginal q 2 g := by
    apply Subtype.ext
    exact congrArg (fun z : CFSG.Models.Chevalley.Model (CartanMatrix.A 2)
      (q.Extension 2) => z.val) he
  rw [← hxg]
  exact CFSGTwistedA2UnipotentArrays.rootGenerated_le_commutator q hq t ht hx

def rankTwoDerivedCover (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    naturalFixed 2 q →* commutator (Fixed 2 q) :=
  (naturalFixedToOriginal q 2).codRestrict _ (rankTwoFixed_mem_derived q hq)

theorem rankTwoDerivedCover_surjective (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Function.Surjective (rankTwoDerivedCover q hq) := by
  intro g
  obtain ⟨u, hact, _, hform⟩ := original_derived_isometric_lift 2 (by decide) q g
  have hu : u ∈ naturalFixed 2 q :=
    unit_fixed_of_isometric (q.Extension 2) 2
      (definingFieldAutomorphism q 2).toRingHom u.val hform
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  apply twistedFixedAction_injective q 2
  change naturalAction (q.Extension 2) 2
    (CFSGTwistedAIntervalSource.elementaryToModel (q.Extension 2) 2 u) =
      twistedDerivedAction 2 q g
  rw [CFSGTwistedAIntervalSource.elementaryToModel_action]
  exact hact

theorem rankTwoOriginalUnipotent_le_derived (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    originalUnipotent 2 q ≤ commutator (Fixed 2 q) := by
  rintro _ ⟨u, rfl⟩
  exact rankTwoFixed_mem_derived q hq ⟨u.val, u.property.2⟩

theorem rankTwo_central_cover_upper (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (g : naturalFixed 2 q)
    (hg : rankTwoDerivedCover q hq g ∈ Subgroup.center (commutator (Fixed 2 q))) :
    (g.val.val : Mat (q.Extension 2) 2).BlockTriangular id := by
  let D := commutator (Fixed 2 q)
  let U := originalUnipotent 2 q
  have hUD : U ≤ D := rankTwoOriginalUnipotent_le_derived q hq
  have hN := (U.subgroupOf D).le_normalizer_map D.subtype
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hUD] at hN
  have hgN : naturalFixedToOriginal q 2 g ∈ Subgroup.normalizer (U : Set _) :=
    hN ⟨rankTwoDerivedCover q hq g, Subgroup.center_le_normalizer _ hg, rfl⟩
  let p : fixedNaturalPullback 2 q :=
    ⟨(naturalFixedToOriginal q 2 g, g.val),
      CFSGTwistedAIntervalSource.elementaryToModel_action (q.Extension 2) 2 g.val⟩
  exact pullback_normalizer_upper q 2 (by decide) p hgN

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
