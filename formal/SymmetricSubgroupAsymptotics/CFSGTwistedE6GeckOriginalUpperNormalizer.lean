import SymmetricSubgroupAsymptotics.CFSGE6GeckGeneratedParabolics
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalCentralKernel
import SymmetricSubgroupAsymptotics.CoprimeTernaryCentralizerLift

/-! The intrinsic upper normalizer of J maps onto the literal ORIGINAL
positive Sylow normalizer. The original kernel is contained in this
upper normalizer, so the subgroup correspondence applies to all its
overgroups. No original automorphism is lifted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalUpperNormalizer
open CFSGE6GeckGeneratedParabolics CFSGTwistedE6GeckOriginalCentralKernel
open CFSGTwistedE6GeckGeneratedPositiveSylow CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

def originalSimpleParabolic (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (a : Fin 4) : Subgroup (CFSG.Models.TwistedE6 q) :=
  (parabolicGenerated (q.Extension 2) (definingFieldAutomorphism q 2) a).map (generatedToOriginal q)

theorem upperGenerated_map_original (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (upperGenerated (q.Extension 2) (definingFieldAutomorphism q 2)).map (generatedToOriginal q)=
      Subgroup.normalizer (originalPositiveSylow q : Set (CFSG.Models.TwistedE6 q)) := by
  have h := CoprimeTernaryCentralizerLift.sylow_map_normalizer_eq
    (generatedToOriginal q) (generatedToOriginal_surjective q) (generatedPositiveSylow q)
  rw [←(generatedPositiveSylow q).coe_coe,generatedPositiveSylow_coe,
    rootPart_positive_original_image] at h
  rw [upperGenerated_eq_normalizer]
  exact h

theorem original_kernel_le_upperGenerated (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    (generatedToOriginal q).ker≤upperGenerated (q.Extension 2) (definingFieldAutomorphism q 2) := by
  rw [upperGenerated_eq_normalizer]
  exact (generatedToOriginal_kernel_le_center q).trans
    (Subgroup.center_le_normalizer (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false :
      Set (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2))))

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalUpperNormalizer
