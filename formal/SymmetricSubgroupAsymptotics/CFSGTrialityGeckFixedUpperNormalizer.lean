import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeRootGenerated
import SymmetricSubgroupAsymptotics.CFSGFixedSubgroupConjugation

/-! Inside any actual intermediate fixed matrix group, the intrinsic
normalizer of the genuine fixed positive group is exactly the ambient
positive-normalizer envelope. A literal fixed regular word forces the
reverse inclusion, uniformly in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedUpperNormalizer
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckMatrixGroupTwist CFSGTrialityGeckSourceWordAction
open CFSGTrialityGeckRegularFixedPositive CFSGTrialityGeckFixedPositiveSylow
open CFSGTrialityGeckAmbientPositiveSylow CFSGTrialityGeckNormalizerEnvelope
open CFSGTrialityGeckRelativeRootGenerated CFSGFixedSubgroupConjugation
open CFSGNormTwoGeckPositivePGroup CFSGSerreQuadraticMatrix
open CFSGCentralTwistedCommutatorLift
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

def fixedRaw (K : Type) [Field K] (sigma : K ≃+* K) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  MatrixGroup K ⊓ fixedSubgroup (unitTwist K sigma)

theorem fixedRootGenerated_le_fixedRaw (K : Type) [Field K] (sigma : K ≃+* K) :
    fixedRootGenerated K sigma ≤ fixedRaw K sigma := by
  have hr (neg : Bool) : rootGroup A hs hp Base Index K neg ≤ MatrixGroup K := by
    change rootGroup A hs hp Base Index K neg ≤ canonicalElementaryGroup
      (CFSGNormTwoGeckIntegralRealization.realizationData A hs hp Base Index) K
    rw [← positive_sup_negative A hs hp Base Index K]
    cases neg
    · exact le_sup_left
    · exact le_sup_right
  exact le_inf (sup_le (inf_le_left.trans (hr false)) (inf_le_left.trans (hr true)))
    (fixedRootGenerated_le_fixed K sigma)

def upperIn (K : Type) [Field K] (L : Subgroup (Matrix GeckIndex GeckIndex K)ˣ) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ := normalizerEnvelope K ⊓ L

theorem regularMatrix_mem_signedFixed (K : Type) [Field K] (sigma : K ≃+* K) :
    (regularMatrix K).val ∈ signedFixed K sigma false := by
  refine ⟨regularMatrix_positive K,?_⟩
  have he := congrArg (fun g : MatrixGroup K => g.val) (regularMatrix_fixed K sigma)
  change (matrixGroupTwist K sigma (regularMatrix K)).val = (regularMatrix K).val at he
  rw [matrixGroupTwist_val] at he
  exact he

theorem upperIn_eq_normalizer_inter (K : Type) [Field K] [Finite K] (sigma : K ≃+* K)
    (L : Subgroup (Matrix GeckIndex GeckIndex K)ˣ) (hL : L ≤ fixedRaw K sigma) :
    upperIn K L = Subgroup.normalizer
      (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ) ⊓ L := by
  apply le_antisymm
  · intro d hdL
    refine ⟨?_,hdL.2⟩
    exact normalizes_inf_fixed (unitTwist K sigma) (Positive K) d
      (hL hdL.2).2 hdL.1.1
  · intro d hdL
    have hdH : d ∈ MatrixGroup K := (hL hdL.2).1
    have hdInv := (Subgroup.normalizer
      (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ)).inv_mem hdL.1
    have hreg := (Subgroup.mem_normalizer_iff.mp hdInv (regularMatrix K).val).mp
      (regularMatrix_mem_signedFixed K sigma)
    have hpositive : d⁻¹ * (regularMatrix K).val * d ∈ Positive K := by
      simpa only [inv_inv] using hreg.1
    let g : MatrixGroup K := ⟨d,hdH⟩
    have hg : g⁻¹ * regularMatrix K * g ∈ AmbientPositive K := hpositive
    have hn := regular_unique_positive K g hg
    exact ⟨ambient_normalizer_map_le K ⟨g,hn,rfl⟩,hdL.2⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedUpperNormalizer
