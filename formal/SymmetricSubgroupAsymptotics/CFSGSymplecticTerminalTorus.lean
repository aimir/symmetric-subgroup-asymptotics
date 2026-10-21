import SymmetricSubgroupAsymptotics.CFSGSymplecticRootParameters
import SymmetricSubgroupAsymptotics.CFSGTypeARootTorus

/-! A genuine terminal long-root torus, displayed as four actual roots
in the literal elementary symplectic group. Its coordinates and scaling
reuse the proved two-coordinate type-A matrix identity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem terminal_positive_coe (K : Type) [Field K] (r : ℕ) (t : K) :
    ((elementaryRoot K (r + 1) false (Fin.last r) t).val : Mat K (r + 1)) =
      Matrix.transvection (Sum.inl (Fin.last r)) (Sum.inr (Fin.last r)) t := by
  change 1 + t • rootMatrix K (r + 1) false (Fin.last r) = _
  simp [rootMatrix, positive, Matrix.transvection, Matrix.smul_single]

theorem terminal_negative_coe (K : Type) [Field K] (r : ℕ) (t : K) :
    ((elementaryRoot K (r + 1) true (Fin.last r) t).val : Mat K (r + 1)) =
      Matrix.transvection (Sum.inr (Fin.last r)) (Sum.inl (Fin.last r)) t := by
  change 1 + t • rootMatrix K (r + 1) true (Fin.last r) = _
  simp [rootMatrix, negative, positive, Matrix.transpose_single,
    Matrix.transvection, Matrix.smul_single]

def terminalTorus (K : Type) [Field K] (r : ℕ) (g : Kˣ) : elementaryRootGroup K (r + 1) :=
  elementaryRoot K (r + 1) false (Fin.last r) ((g : K) - 1) *
    elementaryRoot K (r + 1) true (Fin.last r) 1 *
    elementaryRoot K (r + 1) false (Fin.last r) ((g : K)⁻¹ - 1) *
    elementaryRoot K (r + 1) true (Fin.last r) (-(g : K))

theorem terminalTorus_coe (K : Type) [Field K] (r : ℕ) (g : Kˣ) :
    ((terminalTorus K r g).val : Mat K (r + 1)) = Matrix.diagonal
      (fun x => if x = Sum.inl (Fin.last r) then (g : K)
        else if x = Sum.inr (Fin.last r) then (g : K)⁻¹ else 1) := by
  change ((elementaryRoot K (r + 1) false (Fin.last r) ((g : K) - 1)).val : Mat K (r + 1)) *
      ((elementaryRoot K (r + 1) true (Fin.last r) 1).val : Mat K (r + 1)) *
      ((elementaryRoot K (r + 1) false (Fin.last r) ((g : K)⁻¹ - 1)).val : Mat K (r + 1)) *
      ((elementaryRoot K (r + 1) true (Fin.last r) (-(g : K))).val : Mat K (r + 1)) = _
  rw [terminal_positive_coe, terminal_negative_coe, terminal_positive_coe, terminal_negative_coe]
  exact CFSGTypeAElementaryMatrices.diagonal_pair (by intro h; cases h) (g : K) (Units.ne_zero g)

theorem terminalTorus_inv (K : Type) [Field K] (r : ℕ) (g : Kˣ) :
    (terminalTorus K r g)⁻¹ = terminalTorus K r g⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply Units.ext
  change ((terminalTorus K r g).val : Mat K (r + 1)) *
    ((terminalTorus K r g⁻¹).val : Mat K (r + 1)) = 1
  rw [terminalTorus_coe, terminalTorus_coe, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one']
  congr 1
  funext x
  by_cases hp : x = Sum.inl (Fin.last r) <;>
    by_cases hn : x = Sum.inr (Fin.last r) <;>
    simp_all [Units.val_inv_eq_inv_val, Units.ne_zero g]

theorem terminalTorus_conjugation (K : Type) [Field K] (r : ℕ) (g : Kˣ) (a : K) :
    terminalTorus K r g * elementaryRoot K (r + 1) false (Fin.last r) a *
      (terminalTorus K r g)⁻¹ =
        elementaryRoot K (r + 1) false (Fin.last r) ((g : K) ^ 2 * a) := by
  let hpq : (Sum.inl (Fin.last r) : Index (r + 1)) ≠ Sum.inr (Fin.last r) := by
    intro h
    cases h
  have h := CFSGTypeARootTorus.torus_conjugation hpq g a
  rw [CFSGTypeARootTorus.torus_inv] at h
  have hm := congrArg Subtype.val h
  change (CFSGTypeARootTorus.torus hpq g).val *
    Matrix.transvection (Sum.inl (Fin.last r)) (Sum.inr (Fin.last r)) a *
    (CFSGTypeARootTorus.torus hpq g⁻¹).val =
    Matrix.transvection (Sum.inl (Fin.last r)) (Sum.inr (Fin.last r)) ((g : K) ^ 2 * a) at hm
  rw [CFSGTypeARootTorus.torus_coe, CFSGTypeARootTorus.torus_coe] at hm
  rw [terminalTorus_inv]
  apply Subtype.ext
  apply Units.ext
  change ((terminalTorus K r g).val : Mat K (r + 1)) *
    ((elementaryRoot K (r + 1) false (Fin.last r) a).val : Mat K (r + 1)) *
    ((terminalTorus K r g⁻¹).val : Mat K (r + 1)) =
    ((elementaryRoot K (r + 1) false (Fin.last r) ((g : K) ^ 2 * a)).val : Mat K (r + 1))
  rw [terminalTorus_coe, terminalTorus_coe, terminal_positive_coe, terminal_positive_coe]
  exact hm

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
