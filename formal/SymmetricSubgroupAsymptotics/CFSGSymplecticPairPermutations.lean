import SymmetricSubgroupAsymptotics.CFSGSymplecticCoordinateLongRoots
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.GroupTheory.Perm.Sign

/-! Every simultaneous permutation of the positive and negative
coordinate pairs belongs to the SAME elementary C subgroup. Adjacent
swaps are literal Weyl words corrected by an actual coordinate torus. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def pairedPermutation (r : ℕ) : Equiv.Perm (Fin (r + 1)) →* Equiv.Perm (Index (r + 1)) where
  toFun σ := Equiv.sumCongr σ σ
  map_one' := by ext x; cases x <;> rfl
  map_mul' σ τ := by ext x; cases x <;> rfl

theorem pairedPermutation_point (r : ℕ) (σ : Equiv.Perm (Fin (r + 1)))
    (side : Bool) (i : Fin (r + 1)) :
    pairedPermutation r σ (coordinatePoint r side i) = coordinatePoint r side (σ i) := by
  cases side <;> rfl

def pairPermutationUnit (K : Type) [Field K] (r : ℕ) :
    Equiv.Perm (Fin (r + 1)) →* (Mat K (r + 1))ˣ :=
  ((Matrix.permMatrixHom : Equiv.Perm (Index (r + 1)) →* Mat K (r + 1)).comp
    (pairedPermutation r)).toHomUnits

theorem pairPermutationUnit_basis (K : Type) [Field K] (r : ℕ)
    (σ : Equiv.Perm (Fin (r + 1))) (side : Bool) (i : Fin (r + 1)) :
    (pairPermutationUnit K r σ : Mat K (r + 1)) *ᵥ coordinateBasis K r side i =
      coordinateBasis K r side (σ i) := by
  change ((pairedPermutation r σ)⁻¹).permMatrix K *ᵥ
    Pi.single (coordinatePoint r side i) 1 = Pi.single (coordinatePoint r side (σ i)) 1
  rw [Matrix.permMatrix_mulVec]
  funext x
  have hx : ((pairedPermutation r σ)⁻¹ x = coordinatePoint r side i) ↔
      x = coordinatePoint r side (σ i) := by
    constructor
    · intro h
      have he := congrArg (pairedPermutation r σ) h
      have hinv : pairedPermutation r σ (((pairedPermutation r σ)⁻¹) x) = x :=
        (pairedPermutation r σ).apply_symm_apply x
      rw [hinv, pairedPermutation_point] at he
      exact he
    · intro h
      apply (pairedPermutation r σ).injective
      have hinv : pairedPermutation r σ (((pairedPermutation r σ)⁻¹) x) = x :=
        (pairedPermutation r σ).apply_symm_apply x
      rw [hinv, pairedPermutation_point]
      exact h
  simp only [Function.comp_apply, Pi.single_apply, hx]

theorem coordinateTorus_neg_one_basis (K : Type) [Field K] (r : ℕ)
    (i j : Fin (r + 1)) (side : Bool) :
    (coordinateTorusUnit K r i (-1) : Mat K (r + 1)) *ᵥ coordinateBasis K r side j =
      if j = i then -coordinateBasis K r side j else coordinateBasis K r side j := by
  rw [coordinateTorusUnit_val]
  change Matrix.diagonal (coordinateTorusDiagonal K r i (-1)) *ᵥ
    Pi.single (coordinatePoint r side j) 1 =
      if j = i then -Pi.single (coordinatePoint r side j) 1 else Pi.single (coordinatePoint r side j) 1
  rw [Matrix.diagonal_mulVec_single]
  have hd : coordinateTorusDiagonal K r i (-1) (coordinatePoint r side j) =
      if j = i then (-1 : K) else 1 := by
    cases side <;> simp [coordinateTorusDiagonal, coordinatePoint]
  rw [hd]
  funext x
  by_cases hji : j = i
  · subst j
    by_cases hx : x = coordinatePoint r side i <;> simp [hx, Pi.single_apply]
  · simp [hji, Pi.single_apply]

def adjacentPairWord (K : Type) [Field K] (r : ℕ) (i : Fin r) : (Mat K (r + 1))ˣ :=
  coordinateTorusUnit K r i.castSucc (-1) * (simpleWeyl K (r + 1) i.castSucc).val

theorem adjacentPairWord_basis (K : Type) [Field K] (r : ℕ) (i : Fin r)
    (side : Bool) (j : Fin (r + 1)) :
    (adjacentPairWord K r i : Mat K (r + 1)) *ᵥ coordinateBasis K r side j =
      coordinateBasis K r side (Equiv.swap i.castSucc i.succ j) := by
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = i.val + 1 at hv
    omega
  change ((coordinateTorusUnit K r i.castSucc (-1) : Mat K (r + 1)) *
    ((simpleWeyl K (r + 1) i.castSucc).val : Mat K (r + 1))) *ᵥ _ = _
  rw [← Matrix.mulVec_mulVec]
  by_cases hj : j = i.castSucc
  · subst j
    rw [simpleWeyl_chain_basis_left, coordinateTorus_neg_one_basis,
      if_neg (Ne.symm hne), Equiv.swap_apply_left]
  · by_cases hj' : j = i.succ
    · subst j
      rw [simpleWeyl_chain_basis_right, Matrix.mulVec_neg, coordinateTorus_neg_one_basis,
        if_pos rfl, neg_neg, Equiv.swap_apply_right]
    · rw [simpleWeyl_chain_basis_other K r side i j hj hj', coordinateTorus_neg_one_basis,
        if_neg hj, Equiv.swap_apply_of_ne_of_ne hj hj']

theorem adjacentPairWord_eq_permutation (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    adjacentPairWord K r i = pairPermutationUnit K r (Equiv.swap i.castSucc i.succ) := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro x
  cases x with
  | inl j =>
    have h := (adjacentPairWord_basis K r i false j).trans
      (pairPermutationUnit_basis K r _ false j).symm
    exact h
  | inr j =>
    have h := (adjacentPairWord_basis K r i true j).trans
      (pairPermutationUnit_basis K r _ true j).symm
    exact h

theorem pairPermutationUnit_mem (K : Type) [Field K] (r : ℕ)
    (σ : Equiv.Perm (Fin (r + 1))) : pairPermutationUnit K r σ ∈ elementaryRootGroup K (r + 1) := by
  let M := (elementaryRootGroup K (r + 1)).toSubmonoid.comap (pairPermutationUnit K r)
  have hgen : Set.range (fun i : Fin r => Equiv.swap i.castSucc i.succ) ⊆ M := by
    rintro _ ⟨i, rfl⟩
    change pairPermutationUnit K r (Equiv.swap i.castSucc i.succ) ∈ elementaryRootGroup K (r + 1)
    rw [← adjacentPairWord_eq_permutation]
    exact (elementaryRootGroup K (r + 1)).mul_mem (coordinateTorusUnit_mem K r i.castSucc (-1))
      (simpleWeyl K (r + 1) i.castSucc).property
  have hle : Submonoid.closure (Set.range (fun i : Fin r => Equiv.swap i.castSucc i.succ)) ≤ M :=
    Submonoid.closure_le.mpr hgen
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hle
  exact hle (Submonoid.mem_top σ)

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
