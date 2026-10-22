import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveChains
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexFlagVectors
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPolarForm

/-! The exact actual centre of D flag-unipotent U is its highest
paired-root line in every characteristic. Reverse centrality uses the
SAME original quadratic action and the fixed first exterior pair; no
Sylow or full orthogonal identification is inferred from this result. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexHighestRoot
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPositiveRoots CFSGOrthogonalDIndexPositiveChains
open CFSGOrthogonalDIndexPositiveCentralizer CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDIndexPolarForm CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDGenerationRootArrays
variable (K : Type) [Field K]

private theorem polar_positive_basis {r : ℕ} (i : Fin r) (x : Index r → K) :
    polar K (Pi.single (Sum.inl i) 1) x = x (Sum.inr i) := by
  simp [polar, leftPart, rightPart, Pi.single_apply, dotProduct, eq_comm]

private theorem single_mulVec {r : ℕ} (i j : Index r) (a : K) (x : Index r → K) :
    Matrix.single i j a *ᵥ x = Pi.single i (a * x j) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]
  · have hik : i ≠ k := Ne.symm hk
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, hk, hik]

def highestDirection (s : ℕ) : Mat K (s + 4) := pairedUpper K 0 (secondIndex s)

theorem highestDirection_mulVec (s : ℕ) (x : Index (s + 4) → K) :
    highestDirection K s *ᵥ x = bivector K (firstVector K s) (secondVector K s) x := by
  unfold bivector
  rw [show polar K (firstVector K s) x = x (Sum.inr 0) from polar_positive_basis K 0 x,
    show polar K (secondVector K s) x = x (Sum.inr (secondIndex s)) from
      polar_positive_basis K (secondIndex s) x]
  simp only [highestDirection, pairedUpper, Matrix.sub_mulVec, single_mulVec, one_mul]
  funext k
  simp [firstVector, secondVector, Pi.single_apply, smul_eq_mul]

theorem unipotent_commutes_highestDirection (s : ℕ) (g : unipotent K (s + 4)) :
    (g.val.val : Mat K (s + 4)) * highestDirection K s =
      highestDirection K s * (g.val.val : Mat K (s + 4)) := by
  have hv (x : Index (s + 4) → K) :
      (g.val.val : Mat K (s + 4)) *ᵥ (highestDirection K s *ᵥ x) =
        highestDirection K s *ᵥ ((g.val.val : Mat K (s + 4)) *ᵥ x) := by
    rw [highestDirection_mulVec, highestDirection_mulVec]
    have h := elementary_bivector_covariance K s g.val (firstVector K s) (secondVector K s) x
    rw [unipotent_firstVector, unipotent_secondVector, bivector_shear] at h
    exact h
  apply Matrix.ext_of_mulVec_single
  intro i
  simpa only [Matrix.mulVec_mulVec] using hv (Pi.single i 1)

def highestInU (s : ℕ) (a : K) : unipotent K (s + 4) :=
  pairInU K s 0 (secondIndex s) (zero_ne_second s) a

theorem highestInU_val (s : ℕ) (a : K) :
    ((highestInU K s a).val.val : Mat K (s + 4)) = 1 + a • highestDirection K s :=
  pairInU_val K s 0 (secondIndex s) (zero_ne_second s) a

theorem highestInU_val_plus (s : ℕ) (a : K) :
    ((highestInU K s a).val.val : Mat K (s + 4)) = plusArray 0 (secondIndex s) a := by
  rw [highestInU_val]
  simp only [highestDirection, pairedUpper, smul_sub, Matrix.smul_single,
    smul_eq_mul, mul_one, plusArray]
  abel

theorem highestInU_mem_center (s : ℕ) (a : K) :
    highestInU K s a ∈ Subgroup.center (unipotent K (s + 4)) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (g.val.val : Mat K (s + 4)) * ((highestInU K s a).val.val : Mat K (s + 4)) =
    ((highestInU K s a).val.val : Mat K (s + 4)) * (g.val.val : Mat K (s + 4))
  rw [highestInU_val]
  simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
    unipotent_commutes_highestDirection]

theorem center_eq_highestInU (s : ℕ) (z : unipotent K (s + 4))
    (hz : z ∈ Subgroup.center (unipotent K (s + 4))) : ∃ a : K, z = highestInU K s a := by
  obtain ⟨a, ha⟩ := central_unipotent_highest_shape K s z hz
  refine ⟨a, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [highestInU_val_plus]
  exact ha

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexHighestRoot
