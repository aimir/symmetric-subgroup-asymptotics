import SymmetricSubgroupAsymptotics.CFSGFFourE6NormSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormOppositeImages
import SymmetricSubgroupAsymptotics.CFSGOpposedSimpleImageKernel
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedGeneratedGroup
import SymmetricSubgroupAsymptotics.CFSGE6GeckOpposedImageKernel
import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedPairNormalizer

/-! The actual norm26 kernel lies in the same original Geck diagonal
pair normalizer. The proof uses only nontrivial simple images and opposed
image disjointness, never ordinary F4 simplicity or full-U faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormActionKernelUpper
open CFSGFFourSerreMatrices CFSGFFourE6CharacteristicTwoNormImage
open CFSGFFourE6NormSimpleParameters CFSGFFourE6NormOppositeImages
open CFSGFFourE6FixedGeneratedGroup CFSGOpposedSimpleImageKernel CFSGOpposedSubgroupKernel
open CFSGE6GeckGeneratedParabolics CFSGE6GeckIntermediateOvergroup CFSGE6GeckFixedUpperNormalizer
open CFSGE6GeckFixedPairNormalizer CFSGE6GeckRelativeSimpleHom CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGTwistedE6GeckFixedRangePreimage
open CFSGTwistedE6GeckRelativeOpposition CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6RelativeWeylOrbits CFSGSerreQuadraticWeylWord CFSGSerreQuadraticMatrix
variable (K:Type) [Field K] [Finite K]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

def generatedToFolded : J→*canonicalElementaryGroup realizationData K :=
  Subgroup.inclusion (fixedRootGenerated_le_folded K)

def generatedNormAction : J→*(characteristicNormImage K≃ₗ[K]characteristicNormImage K) :=
  (normAction K).comp (generatedToFolded K)

private theorem rootPart_image_le (neg:Bool) :
    (rootPart K (RingEquiv.refl K) neg).map (generatedNormAction K)≤
      (normSignedPart K neg).map (normAction K) := by
  rintro a ⟨g,hg,rfl⟩
  refine ⟨generatedToFolded K g,?_,rfl⟩
  exact hg.1

theorem generated_opposite_norm_inf [CharP K 2] :
    (rootPart K (RingEquiv.refl K) false).map (generatedNormAction K)⊓
      (rootPart K (RingEquiv.refl K) true).map (generatedNormAction K)=⊥ := by
  apply le_antisymm _ bot_le
  exact (inf_le_inf (rootPart_image_le K false) (rootPart_image_le K true)).trans
    (le_of_eq (norm_opposite_action_inf K))

private def simpleOne (neg:Bool) (a:Fin 4) : J :=
  ⟨orbitParameter K neg a 1,orbitParameter_mem_generated K (RingEquiv.refl K) neg a 1 rfl⟩

omit [Finite K] in
private theorem simpleOne_mem_rootPart (neg:Bool) (a:Fin 4) :
    simpleOne K neg a∈rootPart K (RingEquiv.refl K) neg :=
  ⟨orbitParameter_mem_upper K neg a 1,orbitParameter_fixed K (RingEquiv.refl K) neg a 1 rfl⟩

private theorem simpleOne_action (neg:Bool) (a:Fin 4) :
    generatedNormAction K (simpleOne K neg a)=normAction K (foldedRoot K neg a 1) := by
  apply congrArg (normAction K)
  apply Subtype.ext
  change orbitParameter K neg a 1=canonicalRoot realizationData K neg a 1
  exact (folded_root_eq_orbitParameter K neg a 1).symm

omit [Finite K] in
private theorem orbitParameter_reflection (a:Fin 4) :
    canonicalWord rawData K (orbitWord a)*orbitParameter K false a 1*
      (canonicalWord rawData K (orbitWord a))⁻¹=orbitParameter K true a (-1) := by
  have h:=rawOrbitHom_reflection K (RingEquiv.refl K) a
  rw [rawOrbitHom_one_parameter] at h
  have hi:(rawOrbitHom K (RingEquiv.refl K) true a (Multiplicative.ofAdd 1))⁻¹=
      rawOrbitHom K (RingEquiv.refl K) true a (Multiplicative.ofAdd (-1)) :=
    (map_inv (rawOrbitHom K (RingEquiv.refl K) true a) (Multiplicative.ofAdd 1)).symm
  rw [hi,rawOrbitHom_neg_one_parameter] at h
  exact h

theorem upper_overgroup_image_witness [CharP K 2] (L:Subgroup J)
    (hBL:upperGenerated K (RingEquiv.refl K)<L) :
    ∃n∈L,∃u∈rootPart K (RingEquiv.refl K) false,
      n*u*n⁻¹∈rootPart K (RingEquiv.refl K) true ∧ generatedNormAction K u≠1 := by
  have hs:=(Subgroup.map_lt_map_iff_of_injective (J).subtype_injective).mpr hBL
  rw [upperGenerated_map] at hs
  obtain ⟨a,ha⟩:=exists_simple_weyl_mem_of_upperIn_lt K (RingEquiv.refl K) J (L.map (J).subtype)
    le_rfl (fixedRootGenerated_le_preimage K (RingEquiv.refl K)) hs (Subgroup.map_subtype_le L)
  obtain ⟨n,hn,hnval⟩:=ha
  have hnval':n.val=canonicalWord rawData K (orbitWord a):=hnval
  refine ⟨n,hn,simpleOne K false a,simpleOne_mem_rootPart K false a,?_,?_⟩
  · change n.val*orbitParameter K false a 1*n.val⁻¹∈signedFixed K (RingEquiv.refl K) true
    rw [hnval',orbitParameter_reflection K a]
    exact ⟨orbitParameter_mem_upper K true a (-1),orbitParameter_fixed K (RingEquiv.refl K) true a (-1) rfl⟩
  · rw [simpleOne_action]
    exact norm_simple_one_ne_one K false a

theorem kernel_le_upper [CharP K 2] :
    (generatedNormAction K).ker≤upperGenerated K (RingEquiv.refl K) := by
  apply kernel_le_upper_of_image_witness (generatedNormAction K)
    (rootPart K (RingEquiv.refl K) false) (rootPart K (RingEquiv.refl K) true)
    (upperGenerated K (RingEquiv.refl K)) ?_ (generated_opposite_norm_inf K)
    (upper_overgroup_image_witness K)
  intro b hb
  change generatedNormAction K b∈Subgroup.normalizer
    ((rootPart K (RingEquiv.refl K) false).map (generatedNormAction K):Set _)
  apply (rootPart K (RingEquiv.refl K) false).le_normalizer_map (generatedNormAction K)
  exact ⟨b,(le_of_eq (upperGenerated_eq_normalizer K (RingEquiv.refl K))) hb,rfl⟩

theorem kernel_positive_normalizes [CharP K 2] (g:J) (hg:g∈(generatedNormAction K).ker) :
    g.val∈Subgroup.normalizer (signedFixed K (RingEquiv.refl K) false:Set (Matrix GeckIndex GeckIndex K)ˣ) := by
  have hupper:=kernel_le_upper K hg
  change g.val∈upperIn K J at hupper
  rw [upperIn_eq_normalizer_inter K (RingEquiv.refl K) J
    (fixedRootGenerated_le_preimage K (RingEquiv.refl K))] at hupper
  exact hupper.1

theorem kernel_negative_normalizes [CharP K 2] (g:J) (hg:g∈(generatedNormAction K).ker) :
    g.val∈Subgroup.normalizer (signedFixed K (RingEquiv.refl K) true:Set (Matrix GeckIndex GeckIndex K)ˣ) := by
  let w:J:=CFSGE6GeckOpposedImageKernel.oppositionInGenerated K (RingEquiv.refl K)
  let c:J:=w⁻¹*g*w
  have hcker:c∈(generatedNormAction K).ker := by
    have h:=(inferInstance:(generatedNormAction K).ker.Normal).conj_mem g hg w⁻¹
    simpa only [inv_inv] using h
  have hcpos:=kernel_positive_normalizes K c hcker
  have hN:(Subgroup.normalizer (signedFixed K (RingEquiv.refl K) false:Set (Matrix GeckIndex GeckIndex K)ˣ)).map
      (MulAut.conj (relativeOpposition K)).toMonoidHom=
    Subgroup.normalizer (signedFixed K (RingEquiv.refl K) true:Set (Matrix GeckIndex GeckIndex K)ˣ) :=
    (Subgroup.map_equiv_normalizer_eq (signedFixed K (RingEquiv.refl K) false)
      (MulAut.conj (relativeOpposition K))).trans
        (congrArg (fun S:Subgroup ((Matrix GeckIndex GeckIndex K)ˣ)=>
          Subgroup.normalizer (S:Set ((Matrix GeckIndex GeckIndex K)ˣ)))
          (fixed_positive_image_eq_fixed_negative K (RingEquiv.refl K)))
  rw [←hN]
  refine ⟨c.val,hcpos,?_⟩
  change relativeOpposition K*((relativeOpposition K)⁻¹*g.val*relativeOpposition K)*
    (relativeOpposition K)⁻¹=g.val
  group

theorem kernel_mem_pairNormalizer [CharP K 2] (g:J) (hg:g∈(generatedNormAction K).ker) :
    g.val∈pairNormalizer K (RingEquiv.refl K) :=
  ⟨⟨kernel_positive_normalizes K g hg,kernel_negative_normalizes K g hg⟩,g.property⟩

theorem kernel_isDiag [CharP K 2] (g:J) (hg:g∈(generatedNormAction K).ker) :
    (g.val:Matrix GeckIndex GeckIndex K).IsDiag :=
  pairNormalizer_isDiag K (RingEquiv.refl K) g.val (kernel_mem_pairNormalizer K g hg)

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormActionKernelUpper
