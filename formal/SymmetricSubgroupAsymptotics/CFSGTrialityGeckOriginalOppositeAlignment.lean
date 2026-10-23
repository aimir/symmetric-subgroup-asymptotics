import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPreimageProjection
import SymmetricSubgroupAsymptotics.CFSGQuotientOppositeAlignment

/-! Actual positive-conjugator transitivity descends to the SAME original
simple triality model. The negative target is the exact image of the
literal fixed-negative preimage; no quotient automorphism is lifted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOppositeAlignment
open CFSGTrialityGeckOriginalPreimageProjection CFSGTrialityGeckPreimageOppositeAlignment
open CFSGTrialityGeckDerivedSylowNormalizer CFSGTrialityGeckOriginalRootFamily
open CFSGQuotientOppositeAlignment

def originalNegative (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Subgroup (CFSG.Models.TrialityD4 q) :=
  (preimageNegative q).map (originalPreimageProjection q)

theorem original_opposite_conjugate_by_positive (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (g : CFSG.Models.TrialityD4 q)
    (hdisj : (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q))⊓
      (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)).map (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈(originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)),
      (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)).map (MulAut.conj g).toMonoidHom=
        (originalNegative q).map (MulAut.conj b).toMonoidHom := by
  have h := opposite_alignment_map (originalPreimageProjection q)
    (originalPreimageProjection_surjective q)
    (preimageSylow q : Subgroup (naturalDerivedPreimage q)) (preimageNegative q)
    (preimageSylow q : Subgroup (naturalDerivedPreimage q))
    (originalPreimageProjection_positive_injective q)
    (preimage_opposite_conjugate_by_positive q) g
  rw [originalPreimageProjection_positive_image] at h
  exact h hdisj

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOppositeAlignment
