import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckStabilizerParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalProductTorusAction
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The actual product-torus inner automorphisms lie in the opposed
Sylow stabilizer. Faithful compatible field data bounds their index by
three times the extension-field automorphism count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckTorusStabilizer
open CFSGTwistedE6GeckStabilizerParameters CFSGTwistedE6GeckRelativeProductTorus
open CFSGTwistedE6GeckOriginalProductTorusAction CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGTwistedE6GeckOriginalSimpleParameters
open CFSGTwistedE6GeckOriginalSingletonA2 CFSGE6GeckRelativeScalarTuples
open CFSGE6GeckProductTorusParameters CFSGTwoFieldSemilinearCosetIndex
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGTwistedE6GeckRelativeRootGenerated
open CFSGSerreOrdinaryTwists

private theorem normalizer_conj_map {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (hg : g∈Subgroup.normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom=H := by
  apply SetLike.coe_injective
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hg

def productTorusPairHom (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    relativeScalars (q.Extension 2) (definingFieldAutomorphism q 2)→*pairStabilizer q :=
  (MulAut.conj.comp (originalProductTorus q)).codRestrict (pairStabilizer q) (by
    intro t neg
    have hn := originalProductTorus_normalizes q t neg
    have hm := normalizer_conj_map _ _ hn
    cases neg
    · rw [rootPart_positive_original_image] at hm
      exact hm
    · exact hm)

theorem product_torus_inner (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (r : (productTorusPairHom q).range) :
    r.val.val∈PrimitiveSocleRawStructure.Inner (CFSG.Models.TwistedE6 q) := by
  obtain ⟨t,ht⟩ := r.property
  exact ⟨originalProductTorus q t,congrArg Subtype.val ht⟩

theorem product_torus_index_le (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (productTorusPairHom q).range.index≤3*Nat.card (RingAut (q.Extension 2)) := by
  have hindex := scalar_lift_index_le (Coefficient q).subtype
    (fun j a => pairedOriginalHom q false j (Multiplicative.ofAdd a))
    (fun j a => singletonOriginalHom q false j (Multiplicative.ofAdd a))
    (pairStabilizer q).subtype (parameters_faithful q)
    (pairedScaleHom _ _) (singletonScaleHom _ _) (exists_semilinear_parameters q)
    (productTorusPairHom q) (relativePowerHom _ _)
    (fun t j a => original_product_torus_paired q t j a)
    (fun t j a => original_product_torus_singleton q t j a)
  exact hindex.trans (Nat.mul_le_mul_right _ (relativePowerHom_range_index_le _ _))

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckTorusStabilizer
