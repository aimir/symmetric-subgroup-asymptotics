import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOriginalGeneration
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNormalizerMatrices

/-! The actual determinant-one defining-fixed matrices cover the
original fixed source's derived group. Central elements of that derived
group have upper-triangular natural lifts, from the proved actual Sylow
normalizer. Neither full named-group recognition nor a centre formula
is a hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists

def originalDerivedCover (q : CFSG.PrimePower) (s : ℕ) :
    naturalFixed (s + 3) q →* commutator (Fixed (s + 3) q) :=
  (naturalFixedToOriginal q (s + 3)).codRestrict _ (fun g =>
    original_join_le_derived q s (naturalFixed_image_mem_original_join q (s + 3) g))

theorem originalDerivedCover_surjective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Surjective (originalDerivedCover q s) := by
  intro g
  obtain ⟨u, hact, _, hform⟩ := original_derived_isometric_lift (s + 3) (by omega) q g
  have hu : u ∈ naturalFixed (s + 3) q :=
    unit_fixed_of_isometric (q.Extension 2) (s + 3)
      (definingFieldAutomorphism q 2).toRingHom u.val hform
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  apply twistedFixedAction_injective q (s + 3)
  change naturalAction (q.Extension 2) (s + 3)
    (CFSGTwistedAIntervalSource.elementaryToModel (q.Extension 2) (s + 3) u) =
      twistedDerivedAction (s + 3) q g
  rw [CFSGTwistedAIntervalSource.elementaryToModel_action]
  exact hact

theorem central_cover_upper (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q)
    (hg : originalDerivedCover q s g ∈
      Subgroup.center (commutator (Fixed (s + 3) q))) :
    (g.val.val : Mat (q.Extension 2) (s + 3)).BlockTriangular id := by
  let D := commutator (Fixed (s + 3) q)
  let U := originalUnipotent (s + 3) q
  have hUD : U ≤ D := originalUnipotent_le_derived q s
  have hN := (U.subgroupOf D).le_normalizer_map D.subtype
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hUD] at hN
  have hgN : naturalFixedToOriginal q (s + 3) g ∈ Subgroup.normalizer (U : Set _) :=
    hN ⟨originalDerivedCover q s g, Subgroup.center_le_normalizer _ hg, rfl⟩
  let p : fixedNaturalPullback (s + 3) q :=
    ⟨(naturalFixedToOriginal q (s + 3) g, g.val),
      CFSGTwistedAIntervalSource.elementaryToModel_action (q.Extension 2) (s + 3) g.val⟩
  exact pullback_normalizer_upper q (s + 3) (by omega) p hgN

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
