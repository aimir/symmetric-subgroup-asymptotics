import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

/-! A literal first-two-row restriction hom, retaining actual matrix
units and their inverses. No determinant or classical-group recognition
is needed for this sparse block calculation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAFirstBlock
variable (K : Type) [Field K] (s : ℕ)
abbrev BigMat := Matrix (Fin (s + 4)) (Fin (s + 4)) K
abbrev SmallMat := Matrix (Fin 2) (Fin 2) K

def head (i : Fin 2) : Fin (s + 4) := ⟨i.val, by have := i.isLt; omega⟩
def block (A : BigMat K s) : SmallMat K := A.submatrix (head s) (head s)
def RowsClosed (A : BigMat K s) : Prop :=
  ∀ i : Fin 2, ∀ k : Fin (s + 4), 2 ≤ k.val → A (head s i) k = 0

theorem head_mul_entry (A B : BigMat K s) (hA : RowsClosed K s A)
    (i : Fin 2) (k : Fin (s + 4)) :
    (A * B) (head s i) k = A (head s i) (head s 0) * B (head s 0) k +
      A (head s i) (head s 1) * B (head s 1) k := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hz : ∑ j : Fin (s + 2), A (head s i) j.succ.succ * B j.succ.succ k = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hA i j.succ.succ (by change 2 ≤ j.val + 1 + 1; omega), zero_mul]
  rw [hz, add_zero] <;> rfl

theorem rowsClosed_one : RowsClosed K s (1 : BigMat K s) := by
  intro i k hk
  have hne : head s i ≠ k := by
    intro h
    have he := congrArg (fun a : Fin (s + 4) => a.val) h
    have hi := i.isLt
    change i.val = k.val at he
    omega
  simp only [Matrix.one_apply, if_neg hne]

theorem rowsClosed_mul (A B : BigMat K s) (hA : RowsClosed K s A)
    (hB : RowsClosed K s B) : RowsClosed K s (A * B) := by
  intro i k hk
  rw [head_mul_entry K s A B hA, hB 0 k hk, hB 1 k hk, mul_zero, mul_zero, add_zero]

theorem block_one : block K s (1 : BigMat K s) = 1 := by
  ext i j
  simp only [block, Matrix.submatrix_apply, Matrix.one_apply, head, Fin.ext_iff]

theorem block_mul (A B : BigMat K s) (hA : RowsClosed K s A) :
    block K s (A * B) = block K s A * block K s B := by
  ext i j
  change (A * B) (head s i) (head s j) = _
  rw [head_mul_entry K s A B hA, Matrix.mul_apply, Fin.sum_univ_two] <;> rfl

theorem block_scalar (c : K) : block K s (c • (1 : BigMat K s)) = c • (1 : SmallMat K) := by
  ext i j
  simp only [block, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
    head, Fin.ext_iff]

def rowUnits : Subgroup (BigMat K s)ˣ where
  carrier := {u | RowsClosed K s (u : BigMat K s) ∧ RowsClosed K s (↑(u⁻¹) : BigMat K s)}
  one_mem' := by constructor <;> exact rowsClosed_one K s
  mul_mem' := by
    intro u v hu hv
    constructor
    · exact rowsClosed_mul K s _ _ hu.1 hv.1
    · simpa only [_root_.mul_inv_rev, Units.val_mul] using
        rowsClosed_mul K s _ _ hv.2 hu.2
  inv_mem' := by
    intro u hu
    exact ⟨hu.2, by simpa only [inv_inv] using hu.1⟩

def blockUnit (u : rowUnits K s) : (SmallMat K)ˣ where
  val := block K s (u.val : BigMat K s)
  inv := block K s (↑(u.val⁻¹) : BigMat K s)
  val_inv := by
    rw [← block_mul K s _ _ u.property.1, Units.mul_inv, block_one]
  inv_val := by
    rw [← block_mul K s _ _ u.property.2, Units.inv_mul, block_one]

def blockHom : rowUnits K s →* (SmallMat K)ˣ where
  toFun := blockUnit K s
  map_one' := Units.ext (block_one K s)
  map_mul' u v := Units.ext
    (block_mul K s (u.val : BigMat K s) (v.val : BigMat K s) u.property.1)

end SymmetricSubgroupAsymptotics.CFSGTwistedAFirstBlock
