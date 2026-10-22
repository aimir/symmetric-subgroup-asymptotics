import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentCenterTorus
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentRoots

/-! The original determinant-one chain torus scales the literal
highest B long-root group by every unit of the original field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

private theorem diagonal_single_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (d e : I → K) (i j : I) :
    Matrix.diagonal d * Matrix.single i j 1 * Matrix.diagonal e =
      Matrix.single i j (d i * e j) := by
  ext x y
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases hx : i = x <;> by_cases hy : j = y <;> simp_all

def secondIndex (s : ℕ) : Fin (s + 3) := ⟨1, by omega⟩

def highestRoot (s : ℕ) (a : K) : elementaryRootGroup K (s + 3) :=
  skewElement K (s + 2) 0 (secondIndex s) a

theorem highestRoot_val (h2 : (2 : K) ≠ 0) (s : ℕ) (a : K) :
    ((highestRoot (K := K) s a).val : Mat K (s + 3)) =
      1 + a • (Matrix.single (pos (s + 3) 0) (neg (s + 3) (secondIndex s)) 1 -
        Matrix.single (pos (s + 3) (secondIndex s)) (neg (s + 3) 0) 1) :=
  skewElement_val K h2 (s + 2) 0 (secondIndex s)
    (by intro h; have hv := congrArg Fin.val h; change 0 = 1 at hv; omega) a

theorem highestRoot_mem_unipotent (h2 : (2 : K) ≠ 0) (s : ℕ) (a : K) :
    highestRoot (K := K) s a ∈ unipotent K (s + 3) :=
  skewElement_mem_unipotent K h2 (s + 2) 0 (secondIndex s)
    (by intro h; have hv := congrArg Fin.val h; change 0 = 1 at hv; omega) a

theorem centerTorus_highestRoot_conjugation (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : Kˣ) (a : K) :
    centerTorus K s g * highestRoot s a * (centerTorus K s g)⁻¹ =
      highestRoot s ((g : K) * a) := by
  let Y : Mat K (s + 3) :=
    Matrix.single (pos (s + 3) 0) (neg (s + 3) (secondIndex s)) 1 -
      Matrix.single (pos (s + 3) (secondIndex s)) (neg (s + 3) 0) 1
  have hY : ((centerTorus K s g).val : Mat K (s + 3)) * Y *
      (↑((centerTorus K s g).val⁻¹) : Mat K (s + 3)) = (g : K) • Y := by
    change ((centerTorus K s g).val : Mat K (s + 3)) * Y *
      (((centerTorus K s g)⁻¹).val : Mat K (s + 3)) = _
    rw [centerTorus_inv, centerTorus_val, centerTorus_val]
    dsimp only [Y]
    rw [mul_sub, sub_mul, diagonal_single_diagonal, diagonal_single_diagonal]
    simp [centerTorusWeight, pos, neg, secondIndex, thirdIndex, Fin.ext_iff,
      Units.val_inv_eq_inv_val, Matrix.smul_single, smul_sub, smul_eq_mul]
  apply Subtype.ext
  apply Units.ext
  change ((centerTorus K s g).val : Mat K (s + 3)) *
      ((highestRoot s a).val : Mat K (s + 3)) *
      (↑((centerTorus K s g).val⁻¹) : Mat K (s + 3)) = _
  rw [highestRoot_val h2, highestRoot_val h2]
  change ((centerTorus K s g).val : Mat K (s + 3)) * (1 + a • Y) *
      (↑((centerTorus K s g).val⁻¹) : Mat K (s + 3)) = 1 + ((g : K) * a) • Y
  rw [mul_add, mul_one, add_mul, Units.mul_inv, mul_smul_comm, smul_mul_assoc, hY, smul_smul]
  rw [mul_comm a (g : K)]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
