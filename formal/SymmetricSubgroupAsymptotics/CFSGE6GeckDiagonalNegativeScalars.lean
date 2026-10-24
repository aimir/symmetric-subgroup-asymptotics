import SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalSimpleScalars
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeParameterEntry
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleRootLine

/-! The actual simultaneous ambient E6 normalizer acts by a nonzero
scalar on every negative simple parameter as well. Root-line preservation
and the coefficient-one negative Cartan entry prove this over every field,
without torus recognition or an ordinary group simplicity hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalNegativeScalars
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGSignedCartanReflections
open CFSGExceptionalNormalizerWordIdentity CFSGTwistedE6GeckNormalizerEnvelope
open CFSGNormTwoCoordinateRootNormalizerEnvelope CFSGNormTwoCoordinateNegativeSimpleRootLine
open CFSGNormTwoGeckNegativeParameterEntry CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

theorem diagonal_normalizes_negative_simple (K : Type) [Field K]
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hD : d∈diagonalNormalizer K) (i : Fin 6) :
    d∈Subgroup.normalizer (canonicalRootSubgroup rawData K true i : Set (Matrix GeckIndex GeckIndex K)ˣ) := by
  have hh := diagonalNormalizer_le_normalizer_root A hd hs hp ho K
    E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K)
    (by decide) (negativeIndex A hs hp (E6Index i))
  have hh' : d∈Subgroup.normalizer
      {g : (Matrix GeckIndex GeckIndex K)ˣ |
        g∈CFSGNormTwoCoordinateRootSubgroup.rootSubgroup A hd hs hp ho K
          (negativeIndex A hs hp (E6Index i))} := hh hD
  have hroot : CFSGNormTwoCoordinateRootSubgroup.rootSubgroup A hd hs hp ho K
      (negativeIndex A hs hp (E6Index i))=canonicalRootSubgroup rawData K true i :=
    rootSubgroup_negative_simple_eq_canonical A hd hs hp ho K i
  rw [hroot] at hh'
  exact hh'

theorem exists_negative_simple_scalar (K : Type) [Field K]
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hD : d∈diagonalNormalizer K) (i : Fin 6) :
    ∃c : Kˣ,∀t,d*canonicalRoot rawData K true i t*d⁻¹=
      canonicalRoot rawData K true i ((c:K)*t) := by
  apply CFSGDiagonalParameterizedRootScalar.exists_unit_scalar
    (fun t=>canonicalRoot rawData K true i t)
    (Sum.inl (E6Index i)) (Sum.inr (E6Index i : Roots A))
    (fun t=>negative_parameter_entry A hs hp E6Base E6Index K i t)
    d (diagonalNormalizer_isDiag K d hD)
  intro t
  have hn := diagonal_normalizes_negative_simple K d hD i
  have hx : canonicalRoot rawData K true i t∈canonicalRootSubgroup rawData K true i := ⟨t,rfl⟩
  have hy := (Subgroup.mem_normalizer_iff.mp hn (canonicalRoot rawData K true i t)).mp hx
  obtain ⟨s,he⟩ := hy
  exact ⟨s,he.symm⟩

end SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalNegativeScalars
