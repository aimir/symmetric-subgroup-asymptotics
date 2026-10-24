import SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalScalarReciprocity
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagonalCartan
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoColumnRigidity

/-! The positive simple parameter actions alone faithfully determine an
actual E6 diagonal-normalizer element in characteristic two. Negative
scalars are reciprocal by the literal rank-one constraint, and the proved
Cartan/column rigidity then kills the entire residual. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalPositiveFaithful
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormalizerWordIdentity
open CFSGSignedCartanReflections CFSGTwistedE6GeckNormalizerEnvelope
open CFSGE6GeckDiagonalNegativeScalars CFSGE6GeckDiagonalScalarReciprocity
open CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem commute_of_conjugate_eq {G : Type*} [Group G] (d x : G)
    (h : d*x*d⁻¹=x) : Commute d x := by
  have he := congrArg (fun z : G=>z*d) h
  exact (by simpa only [mul_assoc,inv_mul_cancel,mul_one] using he : d*x=x*d)

theorem diagonal_eq_one_of_positive_simple_fixed (K : Type) [Field K] [CharP K 2]
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hD : d∈diagonalNormalizer K)
    (hpos : ∀i t,d*canonicalRoot rawData K false i t*d⁻¹=canonicalRoot rawData K false i t) : d=1 := by
  have hneg (i : Fin 6) (t : K) :
      d*canonicalRoot rawData K true i t*d⁻¹=canonicalRoot rawData K true i t := by
    obtain ⟨e,he⟩ := exists_negative_simple_scalar K d hD i
    have hc : ∀a,d*canonicalRoot rawData K false i a*d⁻¹=
        canonicalRoot rawData K false i (((1 : Kˣ):K)*a) := by
      intro a
      simpa only [Units.val_one,one_mul] using hpos i a
    have he1 : e=1 := by
      simpa only [inv_one] using negative_scalar_eq_inverse K d i 1 e hc he
    simpa only [he1,Units.val_one,one_mul] using he t
  have hcomm (neg : Bool) (i : Fin 6) (t : K) : Commute d (canonicalRoot rawData K neg i t) := by
    cases neg
    · exact commute_of_conjugate_eq _ _ (hpos i t)
    · exact commute_of_conjugate_eq _ _ (hneg i t)
  have hcartan : ∀j:E6Base.support,(d : Matrix GeckIndex GeckIndex K)*ᵥPi.single (.inl j) 1=
      Pi.single (.inl j) 1 :=
    CFSGNormTwoCoordinateDiagonalCartan.diagonalNormalizer_le_cartanFixer
      A hd hs hp ho K E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K)
        (by decide) hD
  exact CFSGNormTwoCoordinateCharTwoColumnRigidity.diagonal_eq_one A hd hs hp ho K 0 d
    (diagonalNormalizer_isDiag K d hD) hcartan hcomm

end SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalPositiveFaithful
