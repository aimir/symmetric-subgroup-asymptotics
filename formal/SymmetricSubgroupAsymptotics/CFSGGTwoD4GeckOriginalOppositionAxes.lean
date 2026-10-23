import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalNegativeRootAction
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOpposedImageKernel
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOppositionSignedGroups
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! Literal relative opposition swaps the same original opposed pair
and sends each full negative simple range to its positive counterpart.
Its square is retained; no involution assumption is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOppositionAxes
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckOriginalOppositeAlignment
open CFSGGTwoD4GeckOriginalNegativeRootAction CFSGGTwoD4GeckOriginalSimpleParameters
open CFSGGTwoD4GeckOrbitRootGroups CFSGGTwoD4GeckNegativeParabolicIntersection
open CFSGTrialityGeckOpposedImageKernel CFSGTrialityGeckOppositionSignedGroups
open CFSGTrialityGeckRelativeOpposition CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckRootGeneratedPGroup CFSGSubgroupConjugateRestriction
open CFSGFixedSubgroupConjugation CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

private theorem subgroupOf_conjugation {G : Type*} [Group G]
    (L R S : Subgroup G) (hR : R ≤ L) (g : L)
    (he : R.map (MulAut.conj g.val).toMonoidHom = S) :
    (R.subgroupOf L).map (MulAut.conj g).toMonoidHom = S.subgroupOf L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g.val * y.val * g.val⁻¹ ∈ S
    rw [←he]
    exact ⟨y.val, hy, rfl⟩
  · intro hx
    have hxS : x.val ∈ S := hx
    rw [←he] at hxS
    obtain ⟨y, hy, hyx⟩ := hxS
    exact ⟨⟨y, hR hy⟩, hy, Subtype.ext hyx⟩

def originalOpposition : Projective CartanMatrix.G₂ K :=
  generatedToOriginal K (oppositionInGenerated K (RingEquiv.refl K))

theorem original_positive_opposition_map (p : ℕ) [Fact p.Prime] [CharP K p] :
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)).map
      (MulAut.conj (originalOpposition K)).toMonoidHom = originalNegative K := by
  have hh := congrArg (fun S : Subgroup J => S.map (generatedToOriginal K))
    (rootPart_opposition K (RingEquiv.refl K))
  dsimp only at hh
  rw [map_conjugate, ←originalPositiveSylow_coe K p] at hh
  exact hh

theorem original_negative_opposition_map (p : ℕ) [Fact p.Prime] [CharP K p] :
    (originalNegative K).map (MulAut.conj (originalOpposition K)).toMonoidHom =
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)) := by
  have hr : (rootPart K (RingEquiv.refl K) true).map
      (MulAut.conj (oppositionInGenerated K (RingEquiv.refl K))).toMonoidHom =
        rootPart K (RingEquiv.refl K) false := by
    exact subgroupOf_conjugation _ _ _ (signedFixed_le_generated K (RingEquiv.refl K) true)
      (oppositionInGenerated K (RingEquiv.refl K))
      (opposition_signedFixed_map K (RingEquiv.refl K) true)
  have hh := congrArg (fun S : Subgroup J => S.map (generatedToOriginal K)) hr
  dsimp only at hh
  rw [map_conjugate, ←originalPositiveSylow_coe K p] at hh
  exact hh

theorem original_negative_axis_opposition_map (a : Bool) :
    (originalSimpleHom K true a).range.map (MulAut.conj (originalOpposition K)).toMonoidHom =
      (originalSimpleHom K false a).range := by
  have hraw : (fixedOrbitNegative K a).map
      (MulAut.conj (relativeOpposition K)).toMonoidHom = fixedOrbitPositive K a := by
    rw [fixedOrbitNegative, map_inf_fixed _ _ _ (relativeOpposition_fixed K (RingEquiv.refl K)),
      opposition_orbit_negative_map]
    rfl
  have hle : fixedOrbitNegative K a ≤ signedFixed K (RingEquiv.refl K) true := by
    rw [←fixed_negative_inf_simpleParabolic]
    exact inf_le_left
  have hr : (negativeOrbitRootGenerated K a).map
      (MulAut.conj (oppositionInGenerated K (RingEquiv.refl K))).toMonoidHom =
        positiveOrbitRootGenerated K a :=
    subgroupOf_conjugation _ _ _
      (hle.trans (signedFixed_le_generated K (RingEquiv.refl K) true))
      (oppositionInGenerated K (RingEquiv.refl K)) hraw
  have hh := congrArg (fun S : Subgroup J => S.map (generatedToOriginal K)) hr
  dsimp only at hh
  rw [map_conjugate, original_negative_range_generated, original_positive_range_generated] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOppositionAxes
