import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedPermutation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticForm
import SymmetricSubgroupAsymptotics.CFSGTypeAVectorTransitivity

/-! Literal D vector-normalization primitives: the original SL double
action, signed coordinate permutations and actual terminal fork word.
All ranks and scalar signs remain in the original matrix coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexVectorCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGOrthogonalDGenerationSignedPermutation CFSGTypeAMonomialMatrices
open CFSGOrthogonalDGenerationForkAction CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDBinaryElements CFSGMatrixPairRotation
variable (K : Type) [Field K]

def positivePart (r : ℕ) (v : Index r → K) : Fin r → K := v ∘ Sum.inl
def negativePart (r : ℕ) (v : Index r → K) : Fin r → K := v ∘ Sum.inr

theorem double_positivePart (r : ℕ) (A : NaturalSL K r) (v : Index r → K) :
    positivePart K r (((doubleIntoElementary K r A).val : Mat K r) *ᵥ v) =
      A.val *ᵥ positivePart K r v := by
  change positivePart K r (Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose *ᵥ v) = _
  funext i
  simp [positivePart, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem double_negativePart (r : ℕ) (A : NaturalSL K r) (v : Index r → K) :
    negativePart K r (((doubleIntoElementary K r A).val : Mat K r) *ᵥ v) =
      (A⁻¹).val.transpose *ᵥ negativePart K r v := by
  change negativePart K r (Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose *ᵥ v) = _
  funext i
  simp [negativePart, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem monomial_mulVec_apply {I : Type*} [Fintype I] [DecidableEq I]
    (σ : Equiv.Perm I) (d : I → K) (v : I → K) (i : I) :
    (monomial σ d *ᵥ v) i = d i * v (σ i) := by
  simp [Matrix.mulVec, dotProduct, monomial_apply, ite_mul]

theorem signedPermutation_positive (r : ℕ) (b : Fin r) (σ : Equiv.Perm (Fin r))
    (v : Index r → K) (i : Fin r) :
    (((signedPermutationElement K r b σ).val : Mat K r) *ᵥ v) (Sum.inl i) =
      weight K b σ i * v (Sum.inl (σ i)) := by
  rw [signedPermutationElement_coe, monomial_mulVec_apply]
  rfl

theorem signedPermutation_negative (r : ℕ) (b : Fin r) (σ : Equiv.Perm (Fin r))
    (v : Index r → K) (i : Fin r) :
    (((signedPermutationElement K r b σ).val : Mat K r) *ᵥ v) (Sum.inr i) =
      weight K b σ i * v (Sum.inr (σ i)) := by
  rw [signedPermutationElement_coe, monomial_mulVec_apply]
  rfl

theorem rotation_mulVec_left {I : Type*} [Fintype I] [DecidableEq I]
    (p q : I) (hpq : p ≠ q) (v : I → K) : (rotation K p q *ᵥ v) p = -v q := by
  simp [rotation, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.single_mulVec,
    Matrix.one_mulVec, Function.update_apply, Pi.single_apply, hpq, Ne.symm hpq]

theorem rotation_mulVec_other {I : Type*} [Fintype I] [DecidableEq I]
    (p q x : I) (hxp : x ≠ p) (hxq : x ≠ q) (v : I → K) :
    (rotation K p q *ᵥ v) x = v x := by
  simp [rotation, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.single_mulVec,
    Matrix.one_mulVec, Function.update_apply, Pi.single_apply, hxp, hxq, Ne.symm hxp, Ne.symm hxq]

theorem fork_positive_penultimate (s : ℕ) (v : Index (s + 2) → K) :
    (((simpleWeyl K (s + 2) (last s)).val : Mat K (s + 2)) *ᵥ v)
      (Sum.inl (pen s)) = -v (Sum.inr (last s)) := by
  rw [fork_rotations, ← Matrix.mulVec_mulVec,
    rotation_mulVec_left K _ _ (by intro h; cases h),
    rotation_mulVec_other K (Sum.inr (pen s)) (Sum.inl (last s)) (Sum.inr (last s))
      (by intro h; exact pen_ne_last s (Sum.inr.inj h).symm)
      (by intro h; cases h)]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexVectorCoordinates
