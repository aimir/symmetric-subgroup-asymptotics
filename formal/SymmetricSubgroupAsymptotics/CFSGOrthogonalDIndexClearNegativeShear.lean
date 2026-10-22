import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankShears
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexVectorCoordinates

/-! An explicit SAME-group lower alternating shear clears the negative
coordinates after the original positive vector is e0. The actual split-Q
equation supplies its paired negative entry zero, with no division by two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexVectorCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexAllRankShears
open CFSGOrthogonalDIndexParameters CFSGOrthogonalDIndexQuadraticForm CFSGMatrixShearUnits
variable (K : Type) [Field K]

def clearNegativeParameters (s : ℕ) (y : Fin (s + 2) → K) : Parameters K (s + 2) :=
  fun e => if e.2.val = 0 then y e.1 else 0

theorem clearNegative_column (s : ℕ) (y : Fin (s + 2) → K) (hy : y 0 = 0)
    (j : Fin (s + 2)) : alternating (clearNegativeParameters K s y) j 0 = -y j := by
  by_cases hj : j = 0
  · subst j
    simp [alternating_diagonal, hy]
  · have h0j : 0 < j.val := by
      have hn : j.val ≠ 0 := fun he => hj (Fin.ext he)
      omega
    simp [alternating, strictUpper, clearNegativeParameters, h0j]

def clearNegativeElement (s : ℕ) (y : Fin (s + 2) → K) : elementaryRootGroup K (s + 2) :=
  ⟨lower (alternating (clearNegativeParameters K s y)),
    lower_alternating_mem_all_ranks K (s + 2) (by omega) _⟩

theorem clearNegativeElement_action (s : ℕ) (v : Index (s + 2) → K)
    (hp : positivePart K (s + 2) v = Pi.single 0 1)
    (hn : v (Sum.inr (0 : Fin (s + 2))) = 0) :
    ((clearNegativeElement K s (negativePart K (s + 2) v)).val : Mat K (s + 2)) *ᵥ v =
      Pi.single (Sum.inl 0) 1 := by
  let y := negativePart K (s + 2) v
  have hy : y 0 = 0 := hn
  have hcolumn : alternating (clearNegativeParameters K s y) *ᵥ Pi.single 0 1 = -y := by
    funext j
    rw [Matrix.mulVec_single_one]
    exact clearNegative_column K s y hy j
  change Matrix.fromBlocks (1 : Matrix (Fin (s + 2)) (Fin (s + 2)) K) 0
    (alternating (clearNegativeParameters K s y))
    (1 : Matrix (Fin (s + 2)) (Fin (s + 2)) K) *ᵥ v = _
  funext x
  cases x with
  | inl i =>
    simpa [Matrix.fromBlocks_mulVec, Function.comp_def, positivePart, Pi.single_apply,
      eq_comm] using congrFun hp i
  | inr i =>
    simp only [Matrix.fromBlocks_mulVec, Matrix.one_mulVec, Sum.elim_inr]
    change (alternating (clearNegativeParameters K s y) *ᵥ positivePart K (s + 2) v) i + y i = 0
    rw [hp, hcolumn]
    exact neg_add_cancel _

theorem exists_normalize_positive (s : ℕ) (v : Index (s + 2) → K)
    (hp : positivePart K (s + 2) v = Pi.single 0 1) (hs : splitQ K v = 0) :
    ∃ g : elementaryRootGroup K (s + 2),
      (g.val : Mat K (s + 2)) *ᵥ v = Pi.single (Sum.inl 0) 1 := by
  have hn : v (Sum.inr (0 : Fin (s + 2))) = 0 := by
    change positivePart K (s + 2) v ⬝ᵥ negativePart K (s + 2) v = 0 at hs
    rw [hp, single_dotProduct, one_mul] at hs
    exact hs
  exact ⟨clearNegativeElement K s (negativePart K (s + 2) v),
    clearNegativeElement_action K s v hp hn⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexVectorCoordinates
