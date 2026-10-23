import SymmetricSubgroupAsymptotics.CFSGE6GeckOvergroupCellExtraction
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveSylow

/-! The upper envelope inside the actual fixed-action preimage is the
literal normalizer of the fixed upper subgroup there. The reverse
inclusion uses an actual fixed regular word with all six leading
coordinates nonzero, uniformly in the field characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckFixedUpperNormalizer
open CFSGE6GeckOvergroupCellExtraction CFSGTwistedE6GeckFixedRangePreimage
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckNormalizerEnvelope
open CFSGTwistedE6GeckRegularFixedPositive CFSGTwistedE6GeckAmbientPositiveSylow
open CFSGTwistedE6GeckFixedPositiveSylow CFSGCentralTwistedRootNormalizer
open CFSGTwistedE6GeckFixedSimpleTests CFSGSerreQuadraticMatrix

 theorem regularMatrix_mem_signedFixed (K : Type) [Field K] (sigma : K≃+*K) :
    (regularMatrix K).val∈signedFixed K sigma false := by
  have he : (regularMatrix K).val=
      orbitParameter K false 0 1*orbitParameter K false 1 1*
        orbitParameter K false 2 1*orbitParameter K false 3 1 := by
    change canonicalRoot rawData K false 0 1*canonicalRoot rawData K false 5 1*
        canonicalRoot rawData K false 2 1*canonicalRoot rawData K false 4 1*
        canonicalRoot rawData K false 3 1*canonicalRoot rawData K false 1 1=
      (canonicalRoot rawData K false 0 1*canonicalRoot rawData K false 5 1)*
        (canonicalRoot rawData K false 2 1*canonicalRoot rawData K false 4 1)*
        canonicalRoot rawData K false 3 1*canonicalRoot rawData K false 1 1
    simp only [mul_assoc]
  rw [he]
  exact (signedFixed K sigma false).mul_mem
    ((signedFixed K sigma false).mul_mem
      ((signedFixed K sigma false).mul_mem
        (orbitParameter_one_mem_signedFixed K sigma 0)
        (orbitParameter_one_mem_signedFixed K sigma 1))
      (orbitParameter_one_mem_signedFixed K sigma 2))
    (orbitParameter_one_mem_signedFixed K sigma 3)

theorem upperEnvelope_le_fixed_upper_normalizer (K : Type) [Field K] (sigma : K≃+*K) :
    upperEnvelope K sigma ≤
      Subgroup.normalizer (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro d hd u hu
  have hdN : d∈Subgroup.normalizer (Positive K : Set (Matrix GeckIndex GeckIndex K)ˣ) := hd.1.1
  have hdH : d∈MatrixGroup K := ambient_preimage_le_matrixGroup K sigma hd.2
  have huH : u∈MatrixGroup K := signed_rootGroup_le_matrixGroup K false hu.1
  refine ⟨(Subgroup.mem_normalizer_iff.mp hdN u).mp hu.1,?_⟩
  exact conjugate_fixed_of_central_twist (unitTwist K sigma) (MatrixGroup K)
    d u hdH huH hu.2 (ambient_preimage_central_difference K sigma d hd.2)

theorem fixed_upper_normalizer_inter_preimage_le (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) :
    Subgroup.normalizer (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ) ⊓
      ambientFixedRangePreimage K sigma ≤ upperEnvelope K sigma := by
  intro d hd
  have hdH : d∈MatrixGroup K := ambient_preimage_le_matrixGroup K sigma hd.2
  have hdInv := (Subgroup.normalizer
    (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ)).inv_mem hd.1
  have hreg := (Subgroup.mem_normalizer_iff.mp hdInv (regularMatrix K).val).mp
    (regularMatrix_mem_signedFixed K sigma)
  have hpositive : d⁻¹*(regularMatrix K).val*d∈Positive K := by
    simpa only [inv_inv] using hreg.1
  let g : MatrixGroup K := ⟨d,hdH⟩
  have hg : g⁻¹*regularMatrix K*g∈AmbientPositive K := hpositive
  have hn := regular_unique_positive K g hg
  have henv := ambient_normalizer_map_le K ⟨g,hn,rfl⟩
  exact ⟨henv,hd.2⟩

theorem upperEnvelope_eq_fixed_upper_normalizer_inter (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) :
    upperEnvelope K sigma=
      Subgroup.normalizer (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ) ⊓
        ambientFixedRangePreimage K sigma := by
  apply le_antisymm
  · exact le_inf (upperEnvelope_le_fixed_upper_normalizer K sigma) inf_le_right
  · exact fixed_upper_normalizer_inter_preimage_le K sigma

end SymmetricSubgroupAsymptotics.CFSGE6GeckFixedUpperNormalizer
