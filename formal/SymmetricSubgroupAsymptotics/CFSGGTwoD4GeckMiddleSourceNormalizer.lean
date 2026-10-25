import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointNormalizerAction
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddlePositiveShear
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedCommutators
import SymmetricSubgroupAsymptotics.CFSGFixedSubgroupConjugation

/-! The actual endpoint normalizer is restricted to the original
fixed-root generated source before any action on original cosets is used.
The same middle radical is a normal subgroup of that literal intersection;
no arbitrary ambient matrix normalizer is treated as an original element. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleSourceNormalizer
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckShortComplement
open CFSGTrialityGeckMiddleRadicalCardinality
open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates CFSGGTwoD4GeckMiddleEndpointNormalizerAction
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance
variable (K : Type) [Field K] [Finite K]

def sourceNormalizer : Subgroup (Raw K) :=
  Subgroup.normalizer (fixedMiddle K : Set (Raw K)) ⊓ fixedRootGenerated K (RingEquiv.refl K)

theorem fixedMiddle_le_sourceNormalizer : fixedMiddle K ≤ sourceNormalizer K := by
  intro u hu
  exact ⟨(fixedMiddle K).le_normalizer hu,
    signedFixed_le_generated K (RingEquiv.refl K) false
      ⟨CFSGTrialityGeckMiddleFixedCommutators.middle_le_positive K hu.1,hu.2⟩⟩

def radical : Subgroup (sourceNormalizer K) := (fixedMiddle K).subgroupOf (sourceNormalizer K)

instance radical_normal : (radical K).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (fixedMiddle_le_sourceNormalizer K)).mpr inf_le_left

def radicalEquiv : radical K ≃* fixedMiddle K :=
  Subgroup.subgroupOfEquivOfLe (fixedMiddle_le_sourceNormalizer K)

theorem shortWeyl_mem_sourceNormalizer [CharP K 3] : shortWeyl K ∈ sourceNormalizer K :=
  ⟨shortWeyl_normalizes_fixedMiddle K,shortWeyl_mem_generated K (RingEquiv.refl K)⟩

theorem shortOrbit_mem_sourceNormalizer (a : K) :
    shortOrbit K (RingEquiv.refl K) false a ∈ sourceNormalizer K := by
  have hn : shortOrbit K (RingEquiv.refl K) false a ∈
      Subgroup.normalizer (middleRadical K : Set (Raw K)) := by
    rw [middleRadical_eq_shortComplement]
    exact positive_le_normalizer_shortComplement K
      (shortOrbit_mem_rootGroup K (RingEquiv.refl K) false a)
  exact ⟨CFSGFixedSubgroupConjugation.normalizes_inf_fixed
      (unitTwist K (RingEquiv.refl K)) (middleRadical K)
      (shortOrbit K (RingEquiv.refl K) false a)
      (shortOrbit_fixed K (RingEquiv.refl K) false a rfl) hn,
    shortOrbit_mem_generated K (RingEquiv.refl K) false a rfl⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleSourceNormalizer
