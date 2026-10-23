import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedPairNormalizer
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
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalSimpleScalars
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGSignedCartanReflections
open CFSGExceptionalNormalizerWordIdentity
open CFSGTwistedE6GeckNormalizerEnvelope CFSGE6GeckFixedPairNormalizer
open CFSGTwistedE6GeckAmbientPositiveSylow CFSGNormTwoCoordinateRootNormalizerEnvelope
open CFSGNormTwoCoordinateCanonicalSimpleRootLine CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateLeadingFactor CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

theorem diagonal_normalizes_simple (K : Type) [Field K]
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hD : d∈diagonalNormalizer K) (i : Fin 6) :
    d∈Subgroup.normalizer (canonicalRootSubgroup rawData K false i : Set (Matrix GeckIndex GeckIndex K)ˣ) := by
  have hh := diagonalNormalizer_le_normalizer_root A hd hs hp ho K
    E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K)
    (by decide) (E6Index i)
  have hh' : d∈Subgroup.normalizer
      {g : (Matrix GeckIndex GeckIndex K)ˣ |
        g∈CFSGNormTwoCoordinateRootSubgroup.rootSubgroup A hd hs hp ho K (E6Index i)} := hh hD
  have hroot : CFSGNormTwoCoordinateRootSubgroup.rootSubgroup A hd hs hp ho K (E6Index i)=
      canonicalRootSubgroup rawData K false i :=
    rootSubgroup_simple_eq_canonical A hd hs hp ho K i
  rw [hroot] at hh'
  exact hh'

theorem simple_parameter_entry (K : Type) [Field K] (i : Fin 6) (t : K) :
    (canonicalRoot rawData K false i t : Matrix GeckIndex GeckIndex K)
      (Sum.inl (E6Index i)) (Sum.inr (negativeIndex A hs hp (E6Index i)))=t := by
  have hh := congrArg (fun z : Multiplicative (Fin 6→K)=>z.toAdd i)
    (leadingHom_positiveRoot A hd hs hp ho K i t)
  change (canonicalRoot rawData K false i t : Matrix GeckIndex GeckIndex K)
    (Sum.inl (E6Index i)) (Sum.inr (negativeIndex A hs hp (E6Index i)))=
      (Pi.single i t : Fin 6→K) i at hh
  simpa only [Pi.single_eq_same] using hh

theorem exists_simple_scalar (K : Type) [Field K]
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hD : d∈diagonalNormalizer K)
    (hdiag : (d : Matrix GeckIndex GeckIndex K).IsDiag) (i : Fin 6) :
    ∃c:Kˣ,∀t,d*canonicalRoot rawData K false i t*d⁻¹=
      canonicalRoot rawData K false i ((c:K)*t) := by
  apply CFSGDiagonalParameterizedRootScalar.exists_unit_scalar
    (fun t=>canonicalRoot rawData K false i t)
    (Sum.inl (E6Index i)) (Sum.inr (negativeIndex A hs hp (E6Index i)))
    (simple_parameter_entry K i) d hdiag
  intro t
  have hn := diagonal_normalizes_simple K d hD i
  have hx : canonicalRoot rawData K false i t∈canonicalRootSubgroup rawData K false i := ⟨t,rfl⟩
  have hy := (Subgroup.mem_normalizer_iff.mp hn (canonicalRoot rawData K false i t)).mp hx
  obtain ⟨s,he⟩ := hy
  exact ⟨s,he.symm⟩

theorem pairNormalizer_simple_scalar (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hD : d∈pairNormalizer K sigma) (i : Fin 6) :
    ∃c:Kˣ,∀t,d*canonicalRoot rawData K false i t*d⁻¹=
      canonicalRoot rawData K false i ((c:K)*t) :=
  exists_simple_scalar K d (pairNormalizer_le_diagonalNormalizer K sigma hD)
    (pairNormalizer_isDiag K sigma d hD) i

end SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalSimpleScalars
