import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveRoots
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexHighestShear
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble

/-! Positive chain test elements lie in the SAME actual D-unipotent
subgroup. Its arbitrary central element therefore has exactly the
highest paired-root matrix shape, with its original scalar parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveChains
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPositiveRoots CFSGOrthogonalDIndexHighestShear
open CFSGOrthogonalDGenerationSLDouble CFSGOrthogonalDGenerationRootArrays
open CFSGMatrixShearUnits CFSGTypeAElementaryMatrices
variable (K : Type) [Field K]

theorem flag_neg_lt_neg (r : ℕ) (i j : Fin r) :
    flagEquiv r (Sum.inr i) < flagEquiv r (Sum.inr j) ↔ j < i := by
  change r + (Fin.rev i).val < r + (Fin.rev j).val ↔ j.val < i.val
  rw [Nat.add_lt_add_iff_left]
  exact Fin.rev_lt_rev

def chainElement (r : ℕ) (i j : Fin r) (hij : i ≠ j) (a : K) : elementaryRootGroup K r :=
  doubleIntoElementary K r (elementary hij a)

theorem chainElement_val (r : ℕ) (i j : Fin r) (hij : i ≠ j) (a : K) :
    ((chainElement K r i j hij a).val : Mat K r) = chainArray i j a := by
  rw [show ((chainElement K r i j hij a).val : Mat K r) =
    1 + a • chainMatrix K r i j from doubleHom_elementary_val K r i j hij a]
  simp only [chainMatrix, smul_sub, Matrix.smul_single, smul_eq_mul, mul_one, chainArray]
  abel

theorem chainElement_mem_unipotent (r : ℕ) (i j : Fin r) (hij : i < j) (a : K) :
    chainElement K r i j (ne_of_lt hij) a ∈ unipotent K r := by
  have hp : flagEquiv r (Sum.inl i) ≤ flagEquiv r (Sum.inl j) := by
    change i.val ≤ j.val
    exact hij.le
  have hn : flagEquiv r (Sum.inr j) ≤ flagEquiv r (Sum.inr i) :=
    ((flag_neg_lt_neg r j i).mpr hij).le
  refine ⟨?_, ?_⟩
  · change ((chainElement K r i j (ne_of_lt hij) a).val : Mat K r).BlockTriangular (flagEquiv r)
    rw [chainElement_val]
    exact (Matrix.blockTriangular_one.add (Matrix.blockTriangular_single hp a)).sub
      (Matrix.blockTriangular_single hn a)
  · intro x
    change ((chainElement K r i j (ne_of_lt hij) a).val : Mat K r) x x = 1
    rw [chainElement_val]
    cases x with
    | inl k =>
      by_cases hk : k = i
      · subst k
        simp [chainArray, Matrix.single_apply, ne_of_lt hij, ne_of_gt hij]
      · simp [chainArray, Matrix.single_apply, hk, Ne.symm hk]
    | inr k =>
      by_cases hk : k = j
      · subst k
        simp [chainArray, Matrix.single_apply, ne_of_lt hij, ne_of_gt hij]
      · simp [chainArray, Matrix.single_apply, hk, Ne.symm hk]

def chainInU (r : ℕ) (i j : Fin r) (hij : i < j) (a : K) : unipotent K r :=
  ⟨chainElement K r i j (ne_of_lt hij) a, chainElement_mem_unipotent K r i j hij a⟩

theorem central_unipotent_highest_shape (s : ℕ) (z : unipotent K (s + 4))
    (hz : z ∈ Subgroup.center (unipotent K (s + 4))) :
    ∃ a : K, (z.val.val : Mat K (s + 4)) =
      plusArray (0 : Fin (s + 4)) (⟨1, by omega⟩ : Fin (s + 4)) a := by
  let B := (z.val.val : Mat K (s + 4)).submatrix Sum.inl Sum.inr
  have hmat := central_unipotent_is_upper_shear K s z hz
  have hcomm (i j : Fin (s + 4)) (hij : i.val < j.val) :
      (upper B : Mat K (s + 4)) * chainArray i j 1 =
        chainArray i j 1 * (upper B : Mat K (s + 4)) := by
    have h := congrArg (fun v : unipotent K (s + 4) => (v.val.val : Mat K (s + 4)))
      ((Subgroup.mem_center_iff.mp hz) (chainInU K (s + 4) i j hij 1)).symm
    change (z.val.val : Mat K (s + 4)) * ((chainElement K (s + 4) i j _ 1).val : Mat K (s + 4)) =
      ((chainElement K (s + 4) i j _ 1).val : Mat K (s + 4)) * (z.val.val : Mat K (s + 4)) at h
    rw [chainElement_val, hmat] at h
    exact h
  have ha := central_unipotent_upper_alternating K s z hz
  have hb := highest_shape_of_chain_commutation K s B (fun i => (ha i i).1)
    (fun i j => (ha i j).2) hcomm
  refine ⟨B 0 ⟨1, by omega⟩, ?_⟩
  rw [hmat]
  change Matrix.fromBlocks 1 B 0 1 = _
  rw [hb]
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, plusArray, Matrix.single_apply, Matrix.one_apply,
      Matrix.add_apply, Matrix.sub_apply]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveChains
