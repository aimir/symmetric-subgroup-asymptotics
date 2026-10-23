import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootAction
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRankOneWitness
import SymmetricSubgroupAsymptotics.CFSGE6GeckOppositeOrbitCommutation
import SymmetricSubgroupAsymptotics.CFSGSignedSubgroupPermutationAgreement

/-! One and the same actual permutation acts on both signed original
simple-root chart families. Distinct signs/labels commute by the original
EF relation; matching labels have proved noncommuting witnesses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSignedRootAction
open CFSGTwistedE6GeckOriginalRootAction CFSGTwistedE6GeckOriginalRootIntersection
open CFSGTwistedE6GeckOriginalNegativeRootAction CFSGTwistedE6GeckOriginalRankOneWitness
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGE6GeckOppositeOrbitCommutation CFSGSignedSubgroupPermutationAgreement
open CFSGTwistedE6GeckRelativeRootGenerated CFSGSerreOrdinaryTwists

def originalSignedRoot (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (neg : Bool) (a : Fin 4) : Subgroup (CFSG.Models.TwistedE6 q) :=
  if neg then originalNegativeOrbitRoot q a else originalOrbitRoot q a

theorem original_distinct_orbits_opposite_commute (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a b : Fin 4) (hne : a≠b)
    (x : CFSG.Models.TwistedE6 q) (hx : x∈originalOrbitRoot q a)
    (y : CFSG.Models.TwistedE6 q) (hy : y∈originalNegativeOrbitRoot q b) : Commute x y := by
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := hy
  let ju := signedFixedToGenerated q false u
  let jv := signedFixedToGenerated q true v
  have hc := orbit_groups_opposite_commute (q.Extension 2) a b hne u.val hu v.val hv
  have hJ : Commute ju jv := Subtype.ext hc.eq
  change Commute (generatedToOriginal q ju) (generatedToOriginal q jv)
  exact hJ.map (generatedToOriginal q)

theorem exists_original_signed_root_permutation (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    ∃sigma : Equiv.Perm (Fin 4),∀neg : Bool,∀a : Fin 4,
      (originalSignedRoot q neg a).map f.toMonoidHom=originalSignedRoot q neg (sigma a) := by
  obtain ⟨sigma,hpos⟩ := exists_original_root_permutation q f hU hV
  obtain ⟨tau,hneg⟩ := exists_original_negative_root_permutation q f hU hV
  have he : sigma=tau := permutations_agree (originalOrbitRoot q) (originalNegativeOrbitRoot q)
    (original_distinct_orbits_opposite_commute q)
    (fun a=>⟨originalOrbitOne q false a,originalOrbitOne_positive_mem q a,
      originalOrbitOne q true a,originalOrbitOne_negative_mem q a,original_same_orbit_not_commute q a⟩)
    f sigma tau hpos hneg
  subst tau
  refine ⟨sigma,fun neg a=>?_⟩
  cases neg
  · exact hpos a
  · exact hneg a

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSignedRootAction
