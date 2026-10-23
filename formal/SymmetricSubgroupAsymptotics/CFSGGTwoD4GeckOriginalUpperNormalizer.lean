import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedParabolics
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedSylow
import SymmetricSubgroupAsymptotics.CoprimeTernaryCentralizerLift

/-! The literal identity-twist upper normalizer maps onto the actual
original G2 positive Sylow normalizer. The proved original central
kernel lies inside it, enabling honest subgroup correspondence. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalUpperNormalizer
open CFSGGTwoD4GeckOriginalProjection CFSGTrialityGeckGeneratedParabolics
open CFSGTrialityGeckGeneratedSylow CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckRootGeneratedPGroup CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

def originalSimpleParabolic (a : Bool) : Subgroup (Projective CartanMatrix.G₂ K) :=
  (parabolicGenerated K (RingEquiv.refl K) a).map (generatedToOriginal K)

theorem upperGenerated_map_original (p : ℕ) [Fact p.Prime] [CharP K p] :
    (upperGenerated K (RingEquiv.refl K)).map (generatedToOriginal K) =
      Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.G₂ K)) := by
  have h := CoprimeTernaryCentralizerLift.sylow_map_normalizer_eq
    (generatedToOriginal K) (generatedToOriginal_surjective K)
    (positiveSylow K (RingEquiv.refl K) p)
  rw [←(positiveSylow K (RingEquiv.refl K) p).coe_coe, positiveSylow_coe,
    ←originalPositiveSylow_coe K p] at h
  rw [upperGenerated_eq_normalizer]
  exact h

theorem original_kernel_le_upperGenerated :
    (generatedToOriginal K).ker ≤ upperGenerated K (RingEquiv.refl K) := by
  rw [upperGenerated_eq_normalizer]
  exact (generatedToOriginal_kernel_le_center K).trans
    (Subgroup.center_le_normalizer (rootPart K (RingEquiv.refl K) false :
      Set (fixedRootGenerated K (RingEquiv.refl K))))

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalUpperNormalizer
