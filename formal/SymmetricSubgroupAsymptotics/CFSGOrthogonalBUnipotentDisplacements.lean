import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentRoots

/-! Literal displacement equations for actual B unipotent words.
The short-root paired-axis equation retains its genuine quadratic term. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable (K : Type) [Field K]

theorem chain_displacement_pos (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : K) (v : Index n → K) :
    (((chainElement K n i j hij a).val : Mat K n) *ᵥ v - v) (pos n i) = a * v (pos n j) := by
  rw [chainElement_val, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp [Matrix.sub_mulVec, Matrix.single_mulVec, Pi.single_apply, pos, neg]

theorem chain_displacement_neg (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : K) (v : Index n → K) :
    (((chainElement K n i j hij a).val : Mat K n) *ᵥ v - v) (neg n j) = -a * v (neg n i) := by
  rw [chainElement_val, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp [Matrix.sub_mulVec, Matrix.single_mulVec, Pi.single_apply, pos, neg]

theorem short_displacement_pos (s : ℕ) (i : Fin (s + 1)) (a : K) (v : Index (s + 1) → K) :
    (((shortElement K s i a).val : Mat K (s + 1)) *ᵥ v - v) (pos (s + 1) i) =
      a * v (middle (s + 1)) - a ^ 2 * v (neg (s + 1) i) := by
  rw [shortElement_val]
  simp [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.single_mulVec, Pi.single_apply, pos, neg, middle] <;> ring

theorem short_displacement_middle (s : ℕ) (i : Fin (s + 1)) (a : K) (v : Index (s + 1) → K) :
    (((shortElement K s i a).val : Mat K (s + 1)) *ᵥ v - v) (middle (s + 1)) =
      (-2 : K) * a * v (neg (s + 1) i) := by
  rw [shortElement_val]
  simp [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.single_mulVec, Pi.single_apply, pos, neg, middle] <;> ring

theorem skew_displacement_pos (h2 : (2 : K) ≠ 0) (s : ℕ)
    (i j : Fin (s + 1)) (hij : i ≠ j) (a : K) (v : Index (s + 1) → K) :
    (((skewElement K s i j a).val : Mat K (s + 1)) *ᵥ v - v) (pos (s + 1) i) =
      a * v (neg (s + 1) j) := by
  rw [skewElement_val K h2 s i j hij a, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  simp [Matrix.sub_mulVec, Matrix.single_mulVec, Pi.single_apply, pos, neg, hij, Ne.symm hij]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
