import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticForm

/-! The actual quadratic D action preserves its polar pairing and
therefore the paired bivector root operators. This is a direct
original-coordinate covariance identity in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

def polar {r : ℕ} (x y : Index r → K) : K :=
  leftPart K x ⬝ᵥ rightPart K y + leftPart K y ⬝ᵥ rightPart K x

theorem splitQ_add {r : ℕ} (x y : Index r → K) :
    splitQ K (x + y) = splitQ K x + splitQ K y + polar K x y := by
  change (leftPart K x + leftPart K y) ⬝ᵥ (rightPart K x + rightPart K y) = _
  simp only [add_dotProduct, dotProduct_add]
  unfold splitQ polar
  ring

theorem elementary_preserves_polar (s : ℕ) (g : elementaryRootGroup K (s + 4))
    (x y : Index (s + 4) → K) :
    polar K ((g.val : Mat K (s + 4)) *ᵥ x) ((g.val : Mat K (s + 4)) *ᵥ y) = polar K x y := by
  have h := elementary_preserves_splitQ K s g (x + y)
  rw [Matrix.mulVec_add, splitQ_add, splitQ_add,
    elementary_preserves_splitQ K s g x, elementary_preserves_splitQ K s g y] at h
  exact add_left_cancel h

theorem polar_add_left {r : ℕ} (x y z : Index r → K) :
    polar K (x + y) z = polar K x z + polar K y z := by
  change (leftPart K x + leftPart K y) ⬝ᵥ rightPart K z +
    leftPart K z ⬝ᵥ (rightPart K x + rightPart K y) = _
  simp only [add_dotProduct, dotProduct_add]
  unfold polar
  ring

theorem polar_smul_left {r : ℕ} (a : K) (x y : Index r → K) :
    polar K (a • x) y = a * polar K x y := by
  change (a • leftPart K x) ⬝ᵥ rightPart K y + leftPart K y ⬝ᵥ (a • rightPart K x) = _
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  unfold polar
  ring

def bivector {r : ℕ} (u v x : Index r → K) : Index r → K :=
  polar K v x • u - polar K u x • v

theorem bivector_shear {r : ℕ} (u v x : Index r → K) (a : K) :
    bivector K u (v + a • u) x = bivector K u v x := by
  rw [bivector, polar_add_left, polar_smul_left]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, bivector]
  ring

theorem elementary_bivector_covariance (s : ℕ) (g : elementaryRootGroup K (s + 4))
    (u v x : Index (s + 4) → K) :
    (g.val : Mat K (s + 4)) *ᵥ bivector K u v x =
      bivector K ((g.val : Mat K (s + 4)) *ᵥ u) ((g.val : Mat K (s + 4)) *ᵥ v)
        ((g.val : Mat K (s + 4)) *ᵥ x) := by
  unfold bivector
  rw [elementary_preserves_polar, elementary_preserves_polar, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_smul]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPolarForm
