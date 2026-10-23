import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedRangeFactor
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedLiftMembership

/-! Every action of the DERIVED ORIGINAL pinned fixed E6 group has an
actual matrix lift in the genuine fixed-root-generated subgroup. The
retained preimage-commutator membership, rather than fixed-point
surjectivity, is what makes the full-preimage factor theorem applicable. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedRootGeneration
open CFSGTwistedE6GeckFixedRangePreimage CFSGTwistedE6GeckFixedRangeFactor
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckDerivedLiftMembership
open CFSGTwistedE6GeckSourceWordAction CFSGTwistedE6GeckActionRangeTwist
open CFSGTwistedE6FixedA2
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckDiagramCovariance
open CFSGSerreOrdinaryTwists

def preimageEmbedding (K : Type) [Field K] (sigma : K ≃+* K) :
    fixedRangePreimage K sigma →* ambientFixedRangePreimage K sigma where
  toFun := fun x => ⟨x.val.val,⟨x.val,x.property,rfl⟩⟩
  map_one' := rfl
  map_mul' := fun _ _ => rfl

theorem preimage_commutator_element_mem_generated (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) (v : fixedRangePreimage K sigma)
    (hv : v ∈ commutator (fixedRangePreimage K sigma)) :
    v.val.val ∈ fixedRootGenerated K sigma := by
  have hmap : (commutator (fixedRangePreimage K sigma)).map (preimageEmbedding K sigma) ≤
      commutator (ambientFixedRangePreimage K sigma) := by
    simp only [commutator_def,Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have he := hmap ⟨v,hv,rfl⟩
  exact preimage_commutator_map_le_generated K sigma ⟨preimageEmbedding K sigma v,he,rfl⟩

theorem exists_original_derived_lift_in_generated (q : CFSG.PrimePower)
    (g : commutator (Fixed q)) :
    ∃ v : MatrixGroup (q.Extension 2),
      v.val ∈ fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) ∧
      matrixAction (q.Extension 2) v = derivedImageAction q g := by
  obtain ⟨v,hv,_,he⟩ := exists_original_derived_lift_in_commutator q g
  exact ⟨v.val,preimage_commutator_element_mem_generated (q.Extension 2)
    (definingFieldAutomorphism q 2) v hv,he⟩

def generatedAction (K : Type) [Field K] (sigma : K ≃+* K) :
    fixedRootGenerated K sigma →* (Image K ≃ₗ[K] Image K) :=
  (matrixAction K).comp (Subgroup.inclusion (fixedRootGenerated_le_matrixGroup K sigma))

theorem original_derived_range_le_generated_action (q : CFSG.PrimePower) :
    (derivedImageAction q).range ≤
      (generatedAction (q.Extension 2) (definingFieldAutomorphism q 2)).range := by
  rintro _ ⟨g,rfl⟩
  obtain ⟨v,hv,he⟩ := exists_original_derived_lift_in_generated q g
  exact ⟨⟨v.val,hv⟩,he⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedRootGeneration
