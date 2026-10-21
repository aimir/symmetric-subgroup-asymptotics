import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements
import SymmetricSubgroupAsymptotics.CFSGTypeARootTorus
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! The actual D fork torus has the expected four diagonal weights.
The proof reindexes a literal chain-root word by an ambient algebra
equivalence. Membership of that coordinate flip in D is neither needed
nor claimed: the resulting word consists of original D fork roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkTorus
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationSLDouble CFSGTypeAElementaryMatrices
variable (K : Type) [Field K]

def pen (s : ℕ) : Fin (s + 2) := (Fin.last s).castSucc
def last (s : ℕ) : Fin (s + 2) := Fin.last (s + 1)

theorem pen_ne_last (s : ℕ) : pen s ≠ last s := by
  intro h
  have hh := congrArg Fin.val h
  change s = s + 1 at hh
  omega

def forkTorus (s : ℕ) (g : Kˣ) : elementaryRootGroup K (s + 2) :=
  rootElement K (s + 2) false (last s) ((g : K) - 1) *
    rootElement K (s + 2) true (last s) 1 *
    rootElement K (s + 2) false (last s) ((g : K)⁻¹ - 1) *
    rootElement K (s + 2) true (last s) (-(g : K))

def chainDiagonal (s : ℕ) (g : Kˣ) : Index (s + 2) → K
  | Sum.inl i => if i = pen s then g else if i = last s then (g : K)⁻¹ else 1
  | Sum.inr i => if i = pen s then (g : K)⁻¹ else if i = last s then g else 1

def forkDiagonal (s : ℕ) (g : Kˣ) : Index (s + 2) → K
  | Sum.inl i => if i = pen s then g else if i = last s then g else 1
  | Sum.inr i => if i = pen s then (g : K)⁻¹ else if i = last s then (g : K)⁻¹ else 1

def flip (s : ℕ) : Equiv.Perm (Index (s + 2)) :=
  Equiv.swap (Sum.inl (last s)) (Sum.inr (last s))

def flipAlgebra (s : ℕ) : Mat K (s + 2) ≃ₐ[K] Mat K (s + 2) :=
  Matrix.reindexAlgEquiv K K (flip s)

theorem flip_single (s : ℕ) (i j : Index (s + 2)) (a : K) :
    flipAlgebra K s (Matrix.single i j a) = Matrix.single (flip s i) (flip s j) a := by
  change (Matrix.single i j a).submatrix (flip s).symm (flip s).symm = _
  rw [Matrix.submatrix_single_equiv]
  rfl

theorem flip_chain_positive (s : ℕ) (a : K) :
    flipAlgebra K s (doubleMatrix K (s + 2) (elementary (pen_ne_last s) a)) =
      ((rootElement K (s + 2) false (last s) a).val : Mat K (s + 2)) := by
  have hp : previous (s + 2) (last s) = pen s := by
    apply Fin.ext
    dsimp [previous, last, pen]
  change flipAlgebra K s ((doubleHom K (s + 2) (elementary (pen_ne_last s) a) :
    (Mat K (s + 2))ˣ) : Mat K (s + 2)) = _
  rw [doubleHom_elementary_val, map_add, map_one, map_smul, chainMatrix, map_sub,
    flip_single, flip_single]
  change 1 + a • _ = 1 + a • positive K (s + 2) (last s)
  rw [positive, dif_neg (show ¬(last s).val + 1 < s + 2 by dsimp [last]; omega), hp]
  simp [flip, Equiv.swap_apply_def, pen_ne_last s]

theorem flip_chain_negative (s : ℕ) (a : K) :
    flipAlgebra K s (doubleMatrix K (s + 2) (elementary (Ne.symm (pen_ne_last s)) a)) =
      ((rootElement K (s + 2) true (last s) a).val : Mat K (s + 2)) := by
  have hp : previous (s + 2) (last s) = pen s := by
    apply Fin.ext
    dsimp [previous, last, pen]
  change flipAlgebra K s ((doubleHom K (s + 2) (elementary (Ne.symm (pen_ne_last s)) a) :
    (Mat K (s + 2))ˣ) : Mat K (s + 2)) = _
  rw [doubleHom_elementary_val, map_add, map_one, map_smul, chainMatrix, map_sub,
    flip_single, flip_single]
  change 1 + a • _ = 1 + a • negative K (s + 2) (last s)
  rw [negative, positive, dif_neg (show ¬(last s).val + 1 < s + 2 by dsimp [last]; omega), hp]
  simp [flip, Matrix.transpose_sub, Matrix.transpose_single, Equiv.swap_apply_def,
    pen_ne_last s]

theorem doubleMatrix_torus (s : ℕ) (g : Kˣ) :
    doubleMatrix K (s + 2) (CFSGTypeARootTorus.torus (pen_ne_last s) g) =
      Matrix.diagonal (chainDiagonal K s g) := by
  unfold doubleMatrix
  rw [CFSGTypeARootTorus.torus_inv, CFSGTypeARootTorus.torus_coe,
    CFSGTypeARootTorus.torus_coe, Matrix.diagonal_transpose, Matrix.fromBlocks_diagonal]
  congr 1
  funext x
  cases x <;> simp only [chainDiagonal, Sum.elim_inl, Sum.elim_inr,
    Units.val_inv_eq_inv_val, inv_inv]

theorem flip_chainDiagonal (s : ℕ) (g : Kˣ) :
    flipAlgebra K s (Matrix.diagonal (chainDiagonal K s g)) =
      Matrix.diagonal (forkDiagonal K s g) := by
  change (Matrix.diagonal (chainDiagonal K s g)).submatrix (flip s).symm (flip s).symm = _
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  cases x with
  | inl i =>
    by_cases hp : i = pen s <;> by_cases hq : i = last s <;>
      simp_all [Function.comp_apply, flip, chainDiagonal, forkDiagonal,
        Equiv.swap_apply_def, pen_ne_last s, Ne.symm (pen_ne_last s)]
  | inr i =>
    by_cases hp : i = pen s <;> by_cases hq : i = last s <;>
      simp_all [Function.comp_apply, flip, chainDiagonal, forkDiagonal,
        Equiv.swap_apply_def, pen_ne_last s, Ne.symm (pen_ne_last s)]

theorem forkTorus_coe (s : ℕ) (g : Kˣ) :
    ((forkTorus K s g).val : Mat K (s + 2)) = Matrix.diagonal (forkDiagonal K s g) := by
  have hw : flipAlgebra K s
      (doubleMatrix K (s + 2) (CFSGTypeARootTorus.torus (pen_ne_last s) g)) =
        ((forkTorus K s g).val : Mat K (s + 2)) := by
    change flipAlgebra K s (doubleMatrix K (s + 2) _) =
      ((rootElement K (s + 2) false (last s) ((g : K) - 1)).val : Mat K (s + 2)) *
      ((rootElement K (s + 2) true (last s) 1).val : Mat K (s + 2)) *
      ((rootElement K (s + 2) false (last s) ((g : K)⁻¹ - 1)).val : Mat K (s + 2)) *
      ((rootElement K (s + 2) true (last s) (-(g : K))).val : Mat K (s + 2))
    simp only [CFSGTypeARootTorus.torus, doubleMatrix_mul, map_mul,
      flip_chain_positive, flip_chain_negative]
  rw [doubleMatrix_torus, flip_chainDiagonal] at hw
  exact hw.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkTorus
