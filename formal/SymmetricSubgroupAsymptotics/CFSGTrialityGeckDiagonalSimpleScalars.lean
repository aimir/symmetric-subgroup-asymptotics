import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGDiagonalParameterizedRootScalar
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom

/-! The actual opposed fixed-pair normalizer acts by nonzero scalars
on each literal ambient simple parameter. Both root-line preservation
and parameter separation are proved in the original Geck coordinates;
no identification of the diagonal normalizer with a generated torus is
assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckDiagonalSimpleScalars
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckNormalizerEnvelope CFSGTrialityGeckFixedPairNormalizer
open CFSGTrialityGeckAmbientPositiveSylow CFSGNormTwoCoordinateRootNormalizerEnvelope
open CFSGNormTwoCoordinateCanonicalSimpleRootLine CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateLeadingFactor CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
local instance : DecidableEq (Roots (CartanMatrix.D 4)) := Classical.decEq _
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4

theorem diagonal_normalizes_simple (K : Type) [Field K]
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hD : d∈diagonalNormalizer K) (i : Fin 4) :
    d∈Subgroup.normalizer (canonicalRootSubgroup rawData K false i : Set (Matrix GeckIndex GeckIndex K)ˣ) := by
  have hh := diagonalNormalizer_le_normalizer_root A hd hs hp ho K
    cartanSign cartanSign_square cartanSign_pairing (normalizer_word_identity K)
    (by decide) (Index i)
  have hh' : d∈Subgroup.normalizer
      {g : (Matrix GeckIndex GeckIndex K)ˣ |
        g∈CFSGNormTwoCoordinateRootSubgroup.rootSubgroup A hd hs hp ho K (Index i)} := hh hD
  have hroot : CFSGNormTwoCoordinateRootSubgroup.rootSubgroup A hd hs hp ho K (Index i)=
      canonicalRootSubgroup rawData K false i :=
    rootSubgroup_simple_eq_canonical A hd hs hp ho K i
  rw [hroot] at hh'
  exact hh'

theorem simple_parameter_entry (K : Type) [Field K] (i : Fin 4) (t : K) :
    (canonicalRoot rawData K false i t : Matrix GeckIndex GeckIndex K)
      (Sum.inl (Index i)) (Sum.inr (negativeIndex A hs hp (Index i)))=t := by
  have hh := congrArg (fun z : Multiplicative (Fin 4→K)=>z.toAdd i)
    (leadingHom_positiveRoot A hd hs hp ho K i t)
  change (canonicalRoot rawData K false i t : Matrix GeckIndex GeckIndex K)
    (Sum.inl (Index i)) (Sum.inr (negativeIndex A hs hp (Index i)))=
      (Pi.single i t : Fin 4→K) i at hh
  simpa only [Pi.single_eq_same] using hh

theorem exists_simple_scalar (K : Type) [Field K]
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hD : d∈diagonalNormalizer K)
    (hdiag : (d : Matrix GeckIndex GeckIndex K).IsDiag) (i : Fin 4) :
    ∃c:Kˣ,∀t,d*canonicalRoot rawData K false i t*d⁻¹=
      canonicalRoot rawData K false i ((c:K)*t) := by
  apply CFSGDiagonalParameterizedRootScalar.exists_unit_scalar
    (fun t=>canonicalRoot rawData K false i t)
    (Sum.inl (Index i)) (Sum.inr (negativeIndex A hs hp (Index i)))
    (simple_parameter_entry K i) d hdiag
  intro t
  have hn := diagonal_normalizes_simple K d hD i
  have hx : canonicalRoot rawData K false i t∈canonicalRootSubgroup rawData K false i := ⟨t,rfl⟩
  have hy := (Subgroup.mem_normalizer_iff.mp hn (canonicalRoot rawData K false i t)).mp hx
  obtain ⟨s,he⟩ := hy
  exact ⟨s,he.symm⟩

theorem pairNormalizer_simple_scalar (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hD : d∈pairNormalizer K sigma) (i : Fin 4) :
    ∃c:Kˣ,∀t,d*canonicalRoot rawData K false i t*d⁻¹=
      canonicalRoot rawData K false i ((c:K)*t) :=
  exists_simple_scalar K d (pairNormalizer_le_diagonalNormalizer K sigma hD)
    (pairNormalizer_isDiag K sigma d hD) i

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckDiagonalSimpleScalars
