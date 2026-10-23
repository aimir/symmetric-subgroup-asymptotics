import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootIntersection
import SymmetricSubgroupAsymptotics.CFSGE6GeckOppositionParabolicTransport
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMinimalParabolics
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! The ORIGINAL opposite parabolics are the actual opposition images
of the previously intrinsic positive minimal parabolics. Consequently
they are exactly the minimal overgroups of the original negative Sylow
normalizer. No original automorphism is lifted to a source group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalOppositeParabolics
open CFSGTwistedE6GeckOriginalRootIntersection CFSGE6GeckOppositionParabolicTransport
open CFSGTwistedE6GeckOriginalMinimalParabolics CFSGTwistedE6GeckOriginalUpperNormalizer
open CFSGE6GeckGeneratedRootIntersection CFSGE6GeckGeneratedParabolics
open CFSGE6GeckMinimalOvergroups CFSGE6GeckOppositeOrbitParabolic
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckSignedOriginalProjection CFSGTwistedE6GeckProjectiveSylowOrder
open CFSGTwistedE6GeckRelativeRootGenerated CFSGSubgroupConjugateRestriction
open CFSGSurjectiveMinimalOvergroups CFSGSerreOrdinaryTwists

def originalOppositionAut (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    MulAut (CFSG.Models.TwistedE6 q) :=
  MulAut.conj (generatedToOriginal q (oppositionInGenerated q))

theorem original_positive_opposition (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map
      (originalOppositionAut q).toMonoidHom=originalNegative q := by
  have h := congrArg (fun S : Subgroup
      (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2))=>
        S.map (generatedToOriginal q)) (rootPart_opposition q)
  dsimp only at h
  rw [map_conjugate,rootPart_positive_original_image] at h
  exact h

theorem original_upper_normalizer_opposition (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (Subgroup.normalizer (originalPositiveSylow q : Set (CFSG.Models.TwistedE6 q))).map
      (originalOppositionAut q).toMonoidHom=
        Subgroup.normalizer (originalNegative q : Set (CFSG.Models.TwistedE6 q)) :=
  (Subgroup.map_equiv_normalizer_eq
    (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)) (originalOppositionAut q)).trans
      (congrArg (fun S : Subgroup (CFSG.Models.TwistedE6 q)=>
        Subgroup.normalizer (S : Set (CFSG.Models.TwistedE6 q))) (original_positive_opposition q))

theorem original_simpleParabolic_opposition_map (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4) :
    (originalSimpleParabolic q a).map (originalOppositionAut q).toMonoidHom=
      originalOppositeParabolic q a := by
  have h := restrict_conjugate
    (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2))
    (simpleParabolic (q.Extension 2) (fixedRootGenerated (q.Extension 2)
      (definingFieldAutomorphism q 2)) a)
    (oppositeOrbitParabolic (q.Extension 2) (definingFieldAutomorphism q 2) a)
    (simpleParabolic_le_intermediate (q.Extension 2) (definingFieldAutomorphism q 2) _ le_rfl a)
    (oppositeOrbitParabolic_le_generated (q.Extension 2) (definingFieldAutomorphism q 2) a)
    (oppositionInGenerated q)
    (simpleParabolic_opposition_map (q.Extension 2) (definingFieldAutomorphism q 2) a)
  have hh := congrArg (fun S : Subgroup
      (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2))=>
        S.map (generatedToOriginal q)) h
  dsimp only at hh
  rw [map_conjugate] at hh
  exact hh

private theorem opposition_kernel_le_upper (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (originalOppositionAut q).toMonoidHom.ker≤
      Subgroup.normalizer (originalPositiveSylow q : Set (CFSG.Models.TwistedE6 q)) := by
  intro x hx
  have he : x=1 := (originalOppositionAut q).injective (hx.trans (map_one _).symm)
  rw [he]
  exact Subgroup.one_mem _

theorem original_lower_lt_oppositeParabolic (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4) :
    Subgroup.normalizer (originalNegative q : Set (CFSG.Models.TwistedE6 q))<
      originalOppositeParabolic q a := by
  have h := (Subgroup.map_lt_map_iff_of_injective
    (f:=(originalOppositionAut q).toMonoidHom) (originalOppositionAut q).injective).mpr
    (original_upper_lt_simpleParabolic q a)
  rwa [original_upper_normalizer_opposition,original_simpleParabolic_opposition_map] at h

theorem original_oppositeParabolic_minimal (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4)
    (H : Subgroup (CFSG.Models.TwistedE6 q))
    (hBH : Subgroup.normalizer (originalNegative q : Set (CFSG.Models.TwistedE6 q))<H)
    (hHP : H≤originalOppositeParabolic q a) : H=originalOppositeParabolic q a := by
  have h := map_minimal_overgroup (originalOppositionAut q).toMonoidHom
    (originalOppositionAut q).surjective (opposition_kernel_le_upper q)
    (original_upper_lt_simpleParabolic q a) (original_simpleParabolic_minimal q a)
  rw [original_upper_normalizer_opposition,original_simpleParabolic_opposition_map] at h
  exact h H hBH hHP

theorem original_minimal_overgroup_eq_oppositeParabolic (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (H : Subgroup (CFSG.Models.TwistedE6 q))
    (hBH : Subgroup.normalizer (originalNegative q : Set (CFSG.Models.TwistedE6 q))<H)
    (hmin : ∀M : Subgroup (CFSG.Models.TwistedE6 q),
      Subgroup.normalizer (originalNegative q : Set (CFSG.Models.TwistedE6 q))<M→M≤H→M=H) :
    ∃a : Fin 4,H=originalOppositeParabolic q a := by
  have h := minimal_overgroup_family_surjective (originalOppositionAut q).toMonoidHom
    (originalOppositionAut q).surjective (opposition_kernel_le_upper q) (originalSimpleParabolic q)
    (original_minimal_overgroup_eq_simpleParabolic q) H
  rw [original_upper_normalizer_opposition] at h
  obtain ⟨a,ha⟩ := h hBH hmin
  exact ⟨a,ha.trans (original_simpleParabolic_opposition_map q a)⟩

theorem originalOppositeParabolic_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] : Function.Injective (originalOppositeParabolic q) := by
  intro a b he
  apply originalSimpleParabolic_injective q
  apply Subgroup.map_injective (f:=(originalOppositionAut q).toMonoidHom)
    (originalOppositionAut q).injective
  simpa only [original_simpleParabolic_opposition_map] using he

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalOppositeParabolics
