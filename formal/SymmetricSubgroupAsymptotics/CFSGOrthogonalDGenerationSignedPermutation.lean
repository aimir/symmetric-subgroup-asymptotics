import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble
import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices

/-! Actual simultaneous signed coordinate permutations in D, obtained
from the proved natural SL embedding. The signs occur on BOTH paired
coordinates; no individual C coordinate flip is imported into D. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedPermutation
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGTypeAMonomialMatrices
variable (K : Type) [Field K]

def weight {r : ℕ} (b : Fin r) (σ : Equiv.Perm (Fin r)) (i : Fin r) : K :=
  if i = b then (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K) else 1

theorem weight_mul_self {r : ℕ} (b : Fin r) (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    weight K b σ i * weight K b σ i = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    by_cases hib : i = b <;> simp [weight, hs, hib]

private theorem monomial_mul_transpose {I : Type*} [Fintype I] [DecidableEq I]
    (σ : Equiv.Perm I) (d : I → K) (hd : ∀ i, d i * d i = 1) :
    monomial σ d * (monomial σ d).transpose = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, monomial_apply]
  rw [Finset.sum_eq_single (σ i)]
  · by_cases hij : i = j
    · subst j
      simp [hd]
    · have hs : σ j ≠ σ i := fun he => hij (σ.injective he).symm
      simp [hij, hs]
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem signedPermutation_inverse_transpose {r : ℕ} (b : Fin r) (σ : Equiv.Perm (Fin r)) :
    ((CFSGTypeAMonomialMatrices.signedPermutation (F := K) b σ)⁻¹).val.transpose =
      (CFSGTypeAMonomialMatrices.signedPermutation (F := K) b σ).val := by
  let A := CFSGTypeAMonomialMatrices.signedPermutation (F := K) b σ
  have hm : A.val * A.val.transpose = 1 :=
    monomial_mul_transpose K σ (weight K b σ) (weight_mul_self K b σ)
  have hinv : (A⁻¹).val * A.val = 1 :=
    congrArg (fun B : Matrix.SpecialLinearGroup (Fin r) K => B.val) (inv_mul_cancel A)
  have he : (A⁻¹).val = A.val.transpose := by
    calc
      (A⁻¹).val = (A⁻¹).val * 1 := (mul_one _).symm
      _ = (A⁻¹).val * (A.val * A.val.transpose) := by rw [hm]
      _ = ((A⁻¹).val * A.val) * A.val.transpose := (mul_assoc _ _ _).symm
      _ = A.val.transpose := by rw [hinv, one_mul]
  change (A⁻¹).val.transpose = A.val
  rw [he, Matrix.transpose_transpose]

def signedPermutationElement (r : ℕ) (b : Fin r) (σ : Equiv.Perm (Fin r)) :
    elementaryRootGroup K r :=
  doubleIntoElementary K r (CFSGTypeAMonomialMatrices.signedPermutation (F := K) b σ)

theorem signedPermutationElement_coe (r : ℕ) (b : Fin r) (σ : Equiv.Perm (Fin r)) :
    ((signedPermutationElement K r b σ).val : Mat K r) =
      monomial (Equiv.sumCongr σ σ) (Sum.elim (weight K b σ) (weight K b σ)) := by
  change Matrix.fromBlocks (CFSGTypeAMonomialMatrices.signedPermutation (F := K) b σ).val 0 0
    ((CFSGTypeAMonomialMatrices.signedPermutation (F := K) b σ)⁻¹).val.transpose = _
  rw [signedPermutation_inverse_transpose]
  ext x y
  cases x <;> cases y <;>
    simp [CFSGTypeAMonomialMatrices.signedPermutation_coe, monomial_apply,
      Matrix.fromBlocks, weight]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedPermutation
