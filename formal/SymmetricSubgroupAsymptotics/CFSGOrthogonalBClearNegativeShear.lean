import SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexShears

/-! A SAME-group alternating lower shear clears the remaining negative
coordinates once the positive vector is e0 and its paired negative
coordinate is zero. Parameters are explicit literal matrix entries. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIndexShears
open CFSGOrthogonalDIndexParameters CFSGMatrixShearUnits
variable (K : Type) [Field K]

def clearNegativeParameters (s : ℕ) (y : Fin (s + 1) → K) : Parameters K (s + 1) :=
  fun e => if e.2.val = 0 then y e.1 else 0

theorem clearNegative_column (s : ℕ) (y : Fin (s + 1) → K) (hy : y 0 = 0) (j : Fin (s + 1)) :
    alternating (clearNegativeParameters K s y) j 0 = -y j := by
  by_cases hj : j = 0
  · subst j
    simp [alternating_diagonal, hy]
  · have h0j : 0 < j.val := by
      have hne : j.val ≠ 0 := fun h => hj (Fin.ext h)
      omega
    simp [alternating, strictUpper, clearNegativeParameters, h0j]

def clearNegativeElement (h2 : (2 : K) ≠ 0) (s : ℕ) (y : Fin (s + 1) → K) :
    elementaryRootGroup K (s + 1) :=
  ⟨extensionHom K (s + 1) (lower (alternating (clearNegativeParameters K s y))),
    lower_alternating_mem K h2 s (clearNegativeParameters K s y)⟩

theorem clearNegativeElement_val (h2 : (2 : K) ≠ 0) (s : ℕ) (y : Fin (s + 1) → K) :
    ((clearNegativeElement K h2 s y).val : Mat K (s + 1)) =
      Matrix.fromBlocks
        (Matrix.fromBlocks 1 0 (alternating (clearNegativeParameters K s y)) 1) 0 0 1 := rfl

theorem clearNegativeElement_action (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v : Index (s + 1) → K) (hp : positivePart K (s + 1) v = Pi.single 0 1)
    (hn : v (neg (s + 1) 0) = 0) (hm : v (middle (s + 1)) = 0) :
    ((clearNegativeElement K h2 s (negativePart K (s + 1) v)).val : Mat K (s + 1)) *ᵥ v =
      Pi.single (pos (s + 1) 0) 1 := by
  let y := negativePart K (s + 1) v
  have hy : y 0 = 0 := hn
  have hcolumn : alternating (clearNegativeParameters K s y) *ᵥ (Pi.single 0 1) = -y := by
    funext j
    rw [Matrix.mulVec_single_one]
    exact clearNegative_column K s y hy j
  rw [clearNegativeElement_val]
  ext x
  rcases x with (i | i) | ⟨⟩
  · change (Matrix.fromBlocks (Matrix.fromBlocks 1 0
        (alternating (clearNegativeParameters K s y)) 1) 0 0 1 *ᵥ v) (pos (s + 1) i) = _
    simpa [Matrix.fromBlocks_mulVec, pos, Function.comp_def, positivePart,
      Pi.single_apply, eq_comm] using congrFun hp i
  · simp only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.one_mulVec,
      zero_add, add_zero, Sum.elim_inl, Sum.elim_inr]
    change (alternating (clearNegativeParameters K s y) *ᵥ positivePart K (s + 1) v) i +
      negativePart K (s + 1) v i = 0
    rw [hp, hcolumn]
    change -y i + y i = 0
    exact neg_add_cancel _
  · simpa [Matrix.fromBlocks_mulVec, middle, Function.comp_def, Pi.single_apply] using hm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
