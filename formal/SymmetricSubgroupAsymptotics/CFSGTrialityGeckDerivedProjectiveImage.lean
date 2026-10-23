import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveNoncommute
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedSylowNormalizer
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! The literal ORIGINAL simple triality projective model is equivalent
to the central quotient of its SAME Derived action image. A genuinely
noncommuting fixed-positive A2 pair proves nontriviality of that quotient.
The actual soluble Sylow normalizer then transfers to the original model.
Two-conjugate-Sylow generation is not asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedProjectiveImage
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckLongDerivedImage
open CFSGTrialityGeckFixedPositiveDerivedImage CFSGTrialityGeckFixedPositiveNoncommute
open CFSGTrialityGeckDerivedSylowNormalizer CFSGSerreOrdinaryTwists

private theorem center_quotient_nontrivial_of_noncommuting {G : Type*} [Group G]
    (a b : G) (hab : ¬ Commute a b) : Nontrivial (G ⧸ Subgroup.center G) := by
  have ha : a ∉ Subgroup.center G := by
    intro h
    exact hab ((Subgroup.mem_center_iff.mp h b).symm)
  apply nontrivial_of_ne ((QuotientGroup.mk' (Subgroup.center G)) a) 1
  intro h
  exact ha ((QuotientGroup.eq_one_iff a).mp h)

theorem imageProjective_nontrivial (q : CFSG.PrimePower) :
    Nontrivial ((derivedImageAction q).range ⧸ Subgroup.center (derivedImageAction q).range) := by
  obtain ⟨u, v, hu, hv, huv⟩ := exists_fixed_positive_noncommuting_actions
    (q.Extension 3) (definingFieldAutomorphism q 3) q.prime
  let a : (derivedImageAction q).range :=
    ⟨positiveAction (q.Extension 3) u, fixed_positive_action_mem_derived_range q u hu⟩
  let b : (derivedImageAction q).range :=
    ⟨positiveAction (q.Extension 3) v, fixed_positive_action_mem_derived_range q v hv⟩
  apply center_quotient_nontrivial_of_noncommuting a b
  intro h
  apply huv
  exact congrArg (fun x : (derivedImageAction q).range => x.val) h.eq

def originalProjectiveImageEquiv (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    CFSG.Models.TrialityD4 q ≃*
      ((derivedImageAction q).range ⧸ Subgroup.center (derivedImageAction q).range) := by
  let f := derivedImageAction q
  letI : Nontrivial (f.range ⧸ Subgroup.center f.range) := imageProjective_nontrivial q
  change (commutator (CFSGTrialityTripleFixedRoots.Fixed q) ⧸
    Subgroup.center (commutator (CFSGTrialityTripleFixedRoots.Fixed q))) ≃*
      (f.range ⧸ Subgroup.center f.range)
  exact CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    f.rangeRestrict f.rangeRestrict_surjective

theorem original_exists_sylow_soluble_normalizer (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    ∃ P : Sylow q.prime (CFSG.Models.TrialityD4 q),
      IsSolvable (Subgroup.normalizer (P : Set (CFSG.Models.TrialityD4 q))) := by
  let H := (derivedImageAction q).range
  letI : Finite H := Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)
  let e := originalProjectiveImageEquiv q
  let f := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  have hf : Function.Surjective f :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center H))
  exact CFSGSolubleSylowNormalizerSurjective.exists_sylow_soluble_normalizer_map f hf
    (exists_image_sylow_soluble_normalizer q)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedProjectiveImage
