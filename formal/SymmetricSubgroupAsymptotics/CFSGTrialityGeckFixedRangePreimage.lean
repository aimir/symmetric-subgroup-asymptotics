import SymmetricSubgroupAsymptotics.CFSGTrialityGeckActionRangeTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixActionCentralKernel
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeRootGenerated
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckEnvelopeBlocks
import SymmetricSubgroupAsymptotics.CFSGCentralTwistedRootNormalizer

/-! The full preimage of the fixed ACTUAL action range has central
twist difference, by the proved matrix-action kernel theorem. Its
diagonal part normalizes the genuinely fixed positive/negative root
generated subgroup. Arbitrary fixed-point surjectivity is not used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRangePreimage
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckMatrixGroupTwist CFSGTrialityGeckActionRangeTwist
open CFSGTrialityGeckMatrixActionCentralKernel CFSGTrialityGeckNormalizerEnvelope
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckPositiveTwist
open CFSGCentralTwistedCommutatorLift CFSGCentralTwistedRootNormalizer
open CFSGNormTwoGeckPositivePGroup CFSGSerreQuadraticMatrix

def fixedRangePreimage (K : Type) [Field K] (sigma : K ≃+* K) : Subgroup (MatrixGroup K) :=
  (fixedSubgroup (actionRangeTwist K sigma)).comap (matrixRangeProjection K)

def ambientFixedRangePreimage (K : Type) [Field K] (sigma : K ≃+* K) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  (fixedRangePreimage K sigma).map (MatrixGroup K).subtype

theorem signed_rootGroup_le_matrixGroup (K : Type) [Field K] (neg : Bool) :
    rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K neg ≤ MatrixGroup K := by
  change rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K neg ≤ canonicalElementaryGroup
      (CFSGNormTwoGeckIntegralRealization.realizationData (CartanMatrix.D 4)
        (CartanMatrix.D_transpose 4) D4_positive_definite Base Index) K
  rw [←positive_sup_negative (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K]
  cases neg
  · exact le_sup_left
  · exact le_sup_right

theorem fixedRootGenerated_le_matrixGroup (K : Type) [Field K] (sigma : K ≃+* K) :
    fixedRootGenerated K sigma ≤ MatrixGroup K :=
  sup_le (inf_le_left.trans (signed_rootGroup_le_matrixGroup K false))
    (inf_le_left.trans (signed_rootGroup_le_matrixGroup K true))

theorem ambient_preimage_le_matrixGroup (K : Type) [Field K] (sigma : K ≃+* K) :
    ambientFixedRangePreimage K sigma ≤ MatrixGroup K := by
  rintro _ ⟨g,_,rfl⟩
  exact g.property

theorem preimage_central_difference (K : Type) [Field K] (sigma : K ≃+* K)
    (g : MatrixGroup K) (hg : g ∈ fixedRangePreimage K sigma) :
    matrixGroupTwist K sigma g*g⁻¹ ∈ Subgroup.center (MatrixGroup K) := by
  apply matrixRangeProjection_kernel_le_center K
  change matrixRangeProjection K (matrixGroupTwist K sigma g*g⁻¹) = 1
  have hfix : actionRangeTwist K sigma (matrixRangeProjection K g) = matrixRangeProjection K g := hg
  rw [map_mul,map_inv,matrixRangeProjection_twist,hfix,mul_inv_cancel]

theorem preimage_central_twist (K : Type) [Field K] (sigma : K ≃+* K)
    (g : MatrixGroup K) (hg : g ∈ fixedRangePreimage K sigma) :
    ∃ z : MatrixGroup K, z ∈ Subgroup.center (MatrixGroup K) ∧
      unitTwist K sigma g.val = z.val*g.val := by
  refine ⟨matrixGroupTwist K sigma g*g⁻¹,preimage_central_difference K sigma g hg,?_⟩
  change unitTwist K sigma g.val = (matrixGroupTwist K sigma g).val*g.val⁻¹*g.val
  rw [inv_mul_cancel_right,matrixGroupTwist_val]

theorem ambient_preimage_central_difference (K : Type) [Field K] (sigma : K ≃+* K)
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hd : d ∈ ambientFixedRangePreimage K sigma)
    (x : (Matrix GeckIndex GeckIndex K)ˣ) (hx : x ∈ MatrixGroup K) :
    (unitTwist K sigma d*d⁻¹)*x = x*(unitTwist K sigma d*d⁻¹) := by
  obtain ⟨g,hg,rfl⟩ := hd
  have hz := preimage_central_difference K sigma g hg
  have hc := congrArg (fun y : MatrixGroup K => y.val)
    (Subgroup.mem_center_iff.mp hz ⟨x,hx⟩)
  change x*((matrixGroupTwist K sigma g).val*g.val⁻¹) =
    ((matrixGroupTwist K sigma g).val*g.val⁻¹)*x at hc
  rw [matrixGroupTwist_val] at hc
  exact hc.symm

theorem fixedRootGenerated_le_preimage (K : Type) [Field K] (sigma : K ≃+* K) :
    fixedRootGenerated K sigma ≤ ambientFixedRangePreimage K sigma := by
  intro u hu
  have hH := fixedRootGenerated_le_matrixGroup K sigma hu
  let g : MatrixGroup K := ⟨u,hH⟩
  have hfix : matrixGroupTwist K sigma g = g := by
    apply Subtype.ext
    exact fixedRootGenerated_le_fixed K sigma hu
  have hg : g ∈ fixedRangePreimage K sigma := by
    change actionRangeTwist K sigma (matrixRangeProjection K g) = matrixRangeProjection K g
    rw [←matrixRangeProjection_twist,hfix]
  exact ⟨g,hg,rfl⟩

theorem diagonal_preimage_normalizes_generated (K : Type) [Field K] (sigma : K ≃+* K) :
    diagonalNormalizer K ⊓ ambientFixedRangePreimage K sigma ≤
      Subgroup.normalizer (fixedRootGenerated K sigma : Set (Matrix GeckIndex GeckIndex K)ˣ) := by
  exact central_twisted_normalizes_fixed_generated (unitTwist K sigma)
    (MatrixGroup K) (Positive K) (Negative K) (diagonalNormalizer K)
    (ambientFixedRangePreimage K sigma)
    (signed_rootGroup_le_matrixGroup K false) (signed_rootGroup_le_matrixGroup K true)
    (ambient_preimage_le_matrixGroup K sigma)
    (fun _ hd => hd.1.1) (fun _ hd => hd.1.2)
    (ambient_preimage_central_difference K sigma)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRangePreimage
