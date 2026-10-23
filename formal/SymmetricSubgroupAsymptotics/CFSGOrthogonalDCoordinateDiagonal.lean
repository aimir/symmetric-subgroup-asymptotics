import SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixUnits
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailMatrixEmbedding

/-! A literal diagonal on one hyperbolic coordinate pair, and its
transport through the actual first-pair identity extension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDCoordinateDiagonal
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
variable (K : Type) [Field K]

def weightsHom (r : ℕ) (i : Fin r) : Kˣ →* (Index r → Kˣ) where
  toFun c := Sum.elim (fun j => if j = i then c else 1)
    (fun j => if j = i then c⁻¹ else 1)
  map_one' := by
    funext x
    cases x <;> simp
  map_mul' c d := by
    funext x
    rcases x with j | j <;> by_cases h : j = i <;>
      simp [h, mul_comm]

def pairDiagonalHom (r : ℕ) (i : Fin r) : Kˣ →* (Mat K r)ˣ :=
  (CFSGDiagonalMatrixUnits.diagonalHom (Index r) K).comp (weightsHom K r i)

theorem pairDiagonalHom_val (r : ℕ) (i : Fin r) (c : Kˣ) :
    (pairDiagonalHom K r i c : Mat K r) = Matrix.diagonal
      (Sum.elim (fun j => if j = i then (c : K) else 1)
        (fun j => if j = i then (c : K)⁻¹ else 1)) := by
  rw [pairDiagonalHom, MonoidHom.comp_apply, CFSGDiagonalMatrixUnits.diagonalHom_val]
  congr 1
  funext x
  rcases x with j | j <;> by_cases h : j = i <;>
    simp [weightsHom, h, Units.val_inv_eq_inv_val]

theorem tail_pairDiagonalHom (r : ℕ) (i : Fin r) (c : Kˣ) :
    tailUnitHom K r (pairDiagonalHom K r i c) = pairDiagonalHom K (r + 1) i.succ c := by
  have hz (j : Fin r) : (0 : Fin (r + 1)) ≠ j.succ := Ne.symm (Fin.succ_ne_zero j)
  apply Units.ext
  change tailMatrixHom K r (pairDiagonalHom K r i c : Mat K r) = _
  rw [pairDiagonalHom_val, pairDiagonalHom_val]
  ext x y
  obtain ⟨x, rfl⟩ := (tailEquiv r).surjective x
  obtain ⟨y, rfl⟩ := (tailEquiv r).surjective y
  rw [tailMatrixHom_apply_equiv]
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      rcases x with x | x <;> rcases y with y | y <;>
        simp [Matrix.fromBlocks, Matrix.diagonal_apply, tailIndex, (Fin.succ_injective r).eq_iff]
    | inr y =>
      fin_cases y <;> rcases x with x | x <;>
        simp [Matrix.fromBlocks, tailIndex]
  | inr x =>
    cases y with
    | inl y =>
      fin_cases x <;> rcases y with y | y <;>
        simp [Matrix.fromBlocks, Matrix.diagonal_apply, tailIndex, hz]
    | inr y =>
      fin_cases x <;> fin_cases y <;>
        simp [Matrix.fromBlocks, hz]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDCoordinateDiagonal
