import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveNoncommute
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedSylowNormalizer
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! The literal original simple twisted-E6 model is the central quotient
of its SAME Derived action image. Actual noncommuting singleton actions
prove nontriviality. The checked soluble Sylow normalizer transfers;
two-Sylow generation is still separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedProjectiveImage
open CFSGTwistedE6GeckFixedPositiveNoncommute CFSGTwistedE6GeckSingletonDerivedSeeds
open CFSGTwistedE6GeckDerivedSylowNormalizer CFSGTwistedE6FixedA2

local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

private theorem center_quotient_nontrivial_of_noncommuting {G : Type*} [Group G]
    (a b : G) (hab : ¬Commute a b) : Nontrivial (G⧸Subgroup.center G) := by
  have ha : a∉Subgroup.center G := by
    intro h
    exact hab ((Subgroup.mem_center_iff.mp h b).symm)
  apply nontrivial_of_ne ((QuotientGroup.mk' (Subgroup.center G)) a) 1
  intro h
  exact ha ((QuotientGroup.eq_one_iff a).mp h)

theorem imageProjective_nontrivial (q : CFSG.PrimePower) :
    Nontrivial ((derivedImageAction q).range⧸Subgroup.center (derivedImageAction q).range) := by
  let a : (derivedImageAction q).range :=
    ⟨imageAction q (root q false 0 1 (one_fixed q)),
      singleton_positive_action_mem_derived q 0 1 (one_fixed q)⟩
  let b : (derivedImageAction q).range :=
    ⟨imageAction q (root q false 1 1 (one_fixed q)),
      singleton_positive_action_mem_derived q 1 1 (one_fixed q)⟩
  apply center_quotient_nontrivial_of_noncommuting a b
  intro h
  apply singleton_fixed_actions_not_commute q
  exact congrArg (fun x : (derivedImageAction q).range=>x.val) h.eq

def originalProjectiveImageEquiv (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    CFSG.Models.TwistedE6 q≃*
      ((derivedImageAction q).range⧸Subgroup.center (derivedImageAction q).range) := by
  let f := derivedImageAction q
  letI : Nontrivial (f.range⧸Subgroup.center f.range) := imageProjective_nontrivial q
  change (commutator (Fixed q)⧸Subgroup.center (commutator (Fixed q)))≃*
    (f.range⧸Subgroup.center f.range)
  exact CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    f.rangeRestrict f.rangeRestrict_surjective

theorem original_exists_sylow_soluble_normalizer (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    ∃P : Sylow q.prime (CFSG.Models.TwistedE6 q),
      IsSolvable (Subgroup.normalizer (P : Set (CFSG.Models.TwistedE6 q))) := by
  let H := (derivedImageAction q).range
  letI : Finite H := Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)
  let e := originalProjectiveImageEquiv q
  let f := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  have hf : Function.Surjective f :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center H))
  exact CFSGSolubleSylowNormalizerSurjective.exists_sylow_soluble_normalizer_map f hf
    (exists_image_sylow_soluble_normalizer q)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedProjectiveImage
