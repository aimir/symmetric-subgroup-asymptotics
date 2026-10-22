import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Block

/-! Independent parameters for alternating block shears and an actual
upper-unitriangular SL block. Zero diagonal is imposed before skew
symmetry, so the parameterization is valid also in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexParameters

abbrev EntryIndex (r : ℕ) := Σ j : Fin r, Fin j.val
abbrev Parameters (K : Type*) (r : ℕ) := EntryIndex r → K

variable {K : Type*} [CommRing K] {r : ℕ}

def strictUpper (p : Parameters K r) : Matrix (Fin r) (Fin r) K :=
  fun i j => if h : i.val < j.val then p ⟨j, ⟨i.val, h⟩⟩ else 0

def alternating (p : Parameters K r) : Matrix (Fin r) (Fin r) K :=
  strictUpper p - (strictUpper p).transpose

@[simp] theorem strictUpper_apply_lt (p : Parameters K r) (i j : Fin r) (h : i.val < j.val) :
    strictUpper p i j = p ⟨j, ⟨i.val, h⟩⟩ := dif_pos h

@[simp] theorem strictUpper_apply_ge (p : Parameters K r) (i j : Fin r) (h : j.val ≤ i.val) :
    strictUpper p i j = 0 := dif_neg (by omega)

@[simp] theorem alternating_diagonal (p : Parameters K r) (i : Fin r) :
    alternating p i i = 0 := by simp [alternating]

theorem alternating_transpose (p : Parameters K r) :
    (alternating p).transpose = -alternating p := by
  simp only [alternating, Matrix.transpose_sub, Matrix.transpose_transpose]
  abel

theorem alternating_apply_lt (p : Parameters K r) (i j : Fin r) (h : i.val < j.val) :
    alternating p i j = p ⟨j, ⟨i.val, h⟩⟩ := by
  simp [alternating, h, Nat.le_of_lt h]

theorem alternating_injective : Function.Injective (alternating : Parameters K r → _) := by
  intro p q hpq
  funext x
  rcases x with ⟨j, i⟩
  let a : Fin r := ⟨i.val, lt_trans i.isLt j.isLt⟩
  have he := congrArg (fun A : Matrix (Fin r) (Fin r) K => A a j) hpq
  simpa only [alternating_apply_lt _ a j i.isLt] using he

theorem entryIndex_card (r : ℕ) : Nat.card (EntryIndex r) = ∑ i ∈ Finset.range r, i := by
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => i) r

theorem entryIndex_card_twice (r : ℕ) : 2 * Nat.card (EntryIndex r) = r * (r - 1) := by
  rw [entryIndex_card, mul_comm]
  exact Finset.sum_range_id_mul_two r

theorem parameters_card (K : Type*) [Finite K] (r : ℕ) :
    Nat.card (Parameters K r) = Nat.card K ^ Nat.card (EntryIndex r) := Nat.card_fun

variable (K : Type*) [Field K] (r : ℕ)

def upperSL (p : Parameters K r) : Matrix.SpecialLinearGroup (Fin r) K :=
  ⟨1 + strictUpper p, by
    have ht : (1 + strictUpper p).BlockTriangular id := by
      intro i j hji
      have hne : i ≠ j := ne_of_gt hji
      have hval : j.val < i.val := hji
      have hn : ¬i.val < j.val := by omega
      simp [Matrix.add_apply, hne, strictUpper, hn]
    rw [Matrix.det_of_upperTriangular ht]
    simp [Matrix.add_apply]⟩

theorem upperSL_injective : Function.Injective (upperSL K r) := by
  intro p q he
  have hm := congrArg (fun A : Matrix.SpecialLinearGroup (Fin r) K => A.val) he
  have hs : strictUpper p = strictUpper q := add_left_cancel hm
  funext x
  rcases x with ⟨j, i⟩
  let a : Fin r := ⟨i.val, lt_trans i.isLt j.isLt⟩
  have h := congrArg (fun A : Matrix (Fin r) (Fin r) K => A a j) hs
  simpa only [strictUpper_apply_lt _ a j i.isLt] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexParameters
