import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalRootFamily

/-! The two previously proved disjoint actual derived-image Sylows
remain disjoint Sylows in the SAME original model. Their central
quotient is separated by the checked central p-element argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOppositeSylows
open CFSGTrialityGeckOriginalIndexSquare CFSGTrialityGeckOriginalRootFamily
open CFSGTrialityGeckOriginalOrderLower CFSGTrialityGeckDerivedProjectiveImage
open CFSGTrialityGeckFixedPositiveImageSylow CFSGTrialityGeckDerivedSylowNormalizer
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance (q : CFSG.PrimePower) : Finite (DerivedImage q) :=
  Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)

def originalOppositeSylow (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Sylow q.prime (CFSG.Models.TrialityD4 q) :=
  (oppositeSylow q).mapSurjective (f := originalProjection q) (originalProjection_surjective q)

theorem originalProjection_kernel_le_center (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (originalProjection q).ker≤Subgroup.center (DerivedImage q) := by
  intro x hx
  change (originalProjectiveImageEquiv q).symm
    (QuotientGroup.mk' (Subgroup.center (DerivedImage q)) x)=1 at hx
  have hq : QuotientGroup.mk' (Subgroup.center (DerivedImage q)) x=1 := by
    apply (originalProjectiveImageEquiv q).symm.injective
    exact hx.trans (map_one (originalProjectiveImageEquiv q).symm).symm
  exact (QuotientGroup.eq_one_iff x).mp hq

private theorem originalSylow_coe (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q))=
      (imagePositiveSylow q : Subgroup (DerivedImage q)).map (originalProjection q) := rfl

private theorem originalOppositeSylow_coe (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (originalOppositeSylow q : Subgroup (CFSG.Models.TrialityD4 q))=
      (oppositeSylow q : Subgroup (DerivedImage q)).map (originalProjection q) := rfl

theorem original_opposite_sylows_disjoint (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q))⊓
      (originalOppositeSylow q : Subgroup (CFSG.Models.TrialityD4 q))=⊥ := by
  rw [originalSylow_coe,originalOppositeSylow_coe]
  exact CFSGCentralKernelPElements.disjoint_map (originalProjection q) (imagePositiveSylow q)
    (originalProjection_sylow_injective q) (originalProjection_kernel_le_center q)
    (imagePositiveSylow q : Subgroup (DerivedImage q)) (oppositeSylow q : Subgroup (DerivedImage q))
    (imagePositiveSylow q).isPGroup' (oppositeSylow q).isPGroup' (oppositeSylows_disjoint q)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOppositeSylows
