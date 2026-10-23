import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveTwist

/-! Both actual normalizer envelopes are preserved by the literal E6
semilinear twist. The proof uses the checked images of U, V and H. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNormalizerEnvelopeTwist
open CFSGTwistedE6GeckNormalizerEnvelope CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckSourceAction CFSGSerreDiagram

theorem matrixGroup_twist_map (K : Type) [Field K] (sigma : K≃+*K) :
    (MatrixGroup K).map (unitTwist K sigma).toMonoidHom=MatrixGroup K :=
  CFSGSerreQuadraticDiagramFieldTwist.elementary_twist_map rawData e6Permutation
    diagramIndex integer_root_diagram K sigma

theorem normalizer_envelope_twist_mem (K : Type) [Field K] (sigma : K≃+*K)
    (g : (Matrix GeckIndex GeckIndex K)ˣ) (hg : g∈normalizerEnvelope K) :
    unitTwist K sigma g∈normalizerEnvelope K := by
  have hn := Subgroup.le_normalizer_map (unitTwist K sigma).toMonoidHom ⟨g,hg.1,rfl⟩
  change unitTwist K sigma g∈Subgroup.normalizer
    ((Positive K).map (unitTwist K sigma).toMonoidHom : Set (Matrix GeckIndex GeckIndex K)ˣ) at hn
  rw [positive_twist_map K sigma] at hn
  have hh : unitTwist K sigma g∈(MatrixGroup K).map (unitTwist K sigma).toMonoidHom :=
    ⟨g,hg.2,rfl⟩
  rw [matrixGroup_twist_map] at hh
  exact ⟨hn,hh⟩

theorem diagonalNormalizer_twist_mem (K : Type) [Field K] (sigma : K≃+*K)
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hdn : d∈diagonalNormalizer K) :
    unitTwist K sigma d∈diagonalNormalizer K := by
  have he := normalizer_envelope_twist_mem K sigma d (diagonalNormalizer_le_envelope K hdn)
  have hn := Subgroup.le_normalizer_map (unitTwist K sigma).toMonoidHom ⟨d,hdn.1.2,rfl⟩
  change unitTwist K sigma d∈Subgroup.normalizer
    ((SignedUpper K true).map (unitTwist K sigma).toMonoidHom : Set (Matrix GeckIndex GeckIndex K)ˣ) at hn
  rw [signedUpper_twist_map K sigma true] at hn
  exact ⟨⟨he.1,hn⟩,he.2⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNormalizerEnvelopeTwist
