import SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveDirectionClosure
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveChains

/-! An actual D-unipotent matrix commuting with the positive simple
directions already has the unique highest-root shape. This weakens the
input of the checked ambient centre calculation, through sparse matrix
direction propagation, without assuming positive-group generation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveHighestShape
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPositiveCentralizer CFSGOrthogonalDIndexHighestShear
open CFSGOrthogonalDIndexQuadraticShears CFSGOrthogonalDIndexPositiveRoots
open CFSGOrthogonalDGenerationRootArrays CFSGOrthogonalDGenerationSLDouble
open CFSGOrthogonalDIndexQuadraticForm CFSGMatrixShearUnits
variable (K : Type) [Field K]

theorem highest_shape (s : ℕ) (z : unipotent K (s + 4))
    (hA : ∀ i : Fin (s + 4),
      (z.val.val : Mat K (s + 4)) * positive K (s + 4) i =
        positive K (s + 4) i * (z.val.val : Mat K (s + 4))) :
    ∃ a : K, (z.val.val : Mat K (s + 4)) =
      plusArray (0 : Fin (s + 4)) (⟨1, by omega⟩ : Fin (s + 4)) a := by
  let B := (z.val.val : Mat K (s + 4)).submatrix Sum.inl Sum.inr
  have hp := CFSGTwistedDPositiveDirectionClosure.pair_directions K (s + 2)
    (z.val.val : Mat K (s + 4)) hA
  have hmat : (z.val.val : Mat K (s + 4)) = (upper B : Mat K (s + 4)) :=
    upper_of_paired_commutation K s _ (unipotent_lower_left_zero K (s + 4) z) z.property.2 hp
  have hQ (x : Index (s + 4) → K) :
      splitQ K ((upper B : Mat K (s + 4)) *ᵥ x) = splitQ K x := by
    have h := elementary_preserves_splitQ K s z.val x
    rw [hmat] at h
    exact h
  have hdiag (i : Fin (s + 4)) : B i i = 0 :=
    upper_diagonal_zero_of_preserves_splitQ K B hQ i
  have hskew (i j : Fin (s + 4)) : B i j + B j i = 0 :=
    upper_pair_sum_zero_of_preserves_splitQ K B hQ i j
  have hc := CFSGTwistedDPositiveDirectionClosure.chain_directions K (s + 4)
    (z.val.val : Mat K (s + 4)) hA
  have hchain (i j : Fin (s + 4)) (hij : i.val < j.val) :
      (upper B : Mat K (s + 4)) * chainArray i j 1 =
        chainArray i j 1 * (upper B : Mat K (s + 4)) := by
    have h := hc i j hij
    rw [hmat] at h
    have he : chainArray i j (1 : K) = 1 + chainMatrix K (s + 4) i j := by
      simp only [chainArray, chainMatrix]
      abel
    rw [he, mul_add, add_mul, mul_one, one_mul, h]
  have hb := highest_shape_of_chain_commutation K s B hdiag hskew hchain
  refine ⟨B 0 ⟨1, by omega⟩, ?_⟩
  rw [hmat]
  change Matrix.fromBlocks 1 B 0 1 = _
  rw [hb]
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, plusArray, Matrix.single_apply, Matrix.one_apply,
      Matrix.add_apply, Matrix.sub_apply]

end SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveHighestShape
