import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.ON
import SymmetricSubgroupAsymptotics.MatrixModelSelectedRowPeriodTwo
import Mathlib.Tactic.FinCases

/-! A selected ROW-basis swap for the FIRST pinned ON matrix over F3.
Only ROWS0 and1 are certified: their154 coefficients each must be
the other basis vector. Twenty fixed blocks of eight coefficient pairs
are closed kernel obligations; the final six positions wrap to valid
rows. Division/remainder proves complete coverage. No dot product, inverse,
group order or alternate-vector search is involved.
Pinned ON source SHA4ff4ed5f4cf2557739bf673178c3fe818d5e1a2ee25302f12e604b11f1dad2b3.
No heartbeat, recursion or memory option is raised. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGONSelectedRowBasisSwap

abbrev Model := CFSG.Models.MatrixGroups.ON.Model
abbrev V := Fin 154 → ZMod 3

def a : Matrix (Fin 154) (Fin 154) (ZMod 3) :=
  CFSG.Models.MatrixData.matrix 3 154 CFSG.Models.MatrixGroups.ON.rows1

def initial : V := Pi.single (0 : Fin 154) 1
def other : V := Pi.single (1 : Fin 154) 1

def rowAt (b : Fin 20) (j : Fin 8) : Fin 154 :=
  Fin.ofNat 154 (8 * b.val + j.val)

def rowPairAt (j : Fin 154) : Prop :=
  a (0 : Fin 154) j = other j ∧ a (1 : Fin 154) j = initial j

theorem block00 : ∀ j : Fin 8, rowPairAt (rowAt 0 j) := by
  unfold rowPairAt
  decide +kernel

theorem block01 : ∀ j : Fin 8, rowPairAt (rowAt 1 j) := by
  unfold rowPairAt
  decide +kernel

theorem block02 : ∀ j : Fin 8, rowPairAt (rowAt 2 j) := by
  unfold rowPairAt
  decide +kernel

theorem block03 : ∀ j : Fin 8, rowPairAt (rowAt 3 j) := by
  unfold rowPairAt
  decide +kernel

theorem block04 : ∀ j : Fin 8, rowPairAt (rowAt 4 j) := by
  unfold rowPairAt
  decide +kernel

theorem block05 : ∀ j : Fin 8, rowPairAt (rowAt 5 j) := by
  unfold rowPairAt
  decide +kernel

theorem block06 : ∀ j : Fin 8, rowPairAt (rowAt 6 j) := by
  unfold rowPairAt
  decide +kernel

theorem block07 : ∀ j : Fin 8, rowPairAt (rowAt 7 j) := by
  unfold rowPairAt
  decide +kernel

theorem block08 : ∀ j : Fin 8, rowPairAt (rowAt 8 j) := by
  unfold rowPairAt
  decide +kernel

theorem block09 : ∀ j : Fin 8, rowPairAt (rowAt 9 j) := by
  unfold rowPairAt
  decide +kernel

theorem block10 : ∀ j : Fin 8, rowPairAt (rowAt 10 j) := by
  unfold rowPairAt
  decide +kernel

theorem block11 : ∀ j : Fin 8, rowPairAt (rowAt 11 j) := by
  unfold rowPairAt
  decide +kernel

theorem block12 : ∀ j : Fin 8, rowPairAt (rowAt 12 j) := by
  unfold rowPairAt
  decide +kernel

theorem block13 : ∀ j : Fin 8, rowPairAt (rowAt 13 j) := by
  unfold rowPairAt
  decide +kernel

theorem block14 : ∀ j : Fin 8, rowPairAt (rowAt 14 j) := by
  unfold rowPairAt
  decide +kernel

theorem block15 : ∀ j : Fin 8, rowPairAt (rowAt 15 j) := by
  unfold rowPairAt
  decide +kernel

theorem block16 : ∀ j : Fin 8, rowPairAt (rowAt 16 j) := by
  unfold rowPairAt
  decide +kernel

theorem block17 : ∀ j : Fin 8, rowPairAt (rowAt 17 j) := by
  unfold rowPairAt
  decide +kernel

theorem block18 : ∀ j : Fin 8, rowPairAt (rowAt 18 j) := by
  unfold rowPairAt
  decide +kernel

theorem block19 : ∀ j : Fin 8, rowPairAt (rowAt 19 j) := by
  unfold rowPairAt
  decide +kernel

theorem block_pairs (b : Fin 20) (j : Fin 8) : rowPairAt (rowAt b j) := by
  fin_cases b
  · exact block00 j
  · exact block01 j
  · exact block02 j
  · exact block03 j
  · exact block04 j
  · exact block05 j
  · exact block06 j
  · exact block07 j
  · exact block08 j
  · exact block09 j
  · exact block10 j
  · exact block11 j
  · exact block12 j
  · exact block13 j
  · exact block14 j
  · exact block15 j
  · exact block16 j
  · exact block17 j
  · exact block18 j
  · exact block19 j

theorem row_pair (i : Fin 154) : rowPairAt i := by
  let b : Fin 20 := ⟨i.val / 8,by omega⟩
  let j : Fin 8 := ⟨i.val % 8,Nat.mod_lt _ (by decide)⟩
  have hi : rowAt b j = i := by
    apply Fin.ext
    change (8 * (i.val / 8) + i.val % 8) % 154 = i.val
    have he : 8 * (i.val / 8) + i.val % 8 = i.val := by omega
    rw [he,Nat.mod_eq_of_lt i.isLt]
  rw [←hi]
  exact block_pairs b j

theorem row_zero : ∀ j : Fin 154, a (0 : Fin 154) j = other j :=
  fun j => (row_pair j).1

theorem row_one : ∀ j : Fin 154, a (1 : Fin 154) j = initial j :=
  fun j => (row_pair j).2

private theorem basis_vecMul_of_row {n : ℕ} {R : Type*} [Semiring R]
    (A : Matrix (Fin n) (Fin n) R) (i : Fin n) (v : Fin n → R)
    (h : ∀ j, A i j = v j) : Pi.single i 1 ᵥ* A = v := by
  rw [Matrix.single_one_vecMul]
  exact funext h

theorem first_row_basis_swap : initial ᵥ* a = other :=
  basis_vecMul_of_row a 0 other row_zero

theorem second_row_basis_swap : other ᵥ* a = initial :=
  basis_vecMul_of_row a 1 initial row_one

theorem row_return_two : (initial ᵥ* a) ᵥ* a = initial := by
  rw [first_row_basis_swap,second_row_basis_swap]

theorem row_nonreturn_one : initial ᵥ* a ≠ initial := by
  have hne : other (0 : Fin 154) ≠ initial 0 := by decide +kernel
  intro h
  have ho : other = initial := first_row_basis_swap.symm.trans h
  exact hne (congrFun ho (0 : Fin 154))

theorem exists_two_dvd_orderOf (hn : ¬IsMulCommutative Model) :
    ∃ g : Model, 2 ∣ orderOf g :=
  MatrixModelSelectedRowPeriodTwo.exists_two_dvd_orderOf 3 154
    CFSG.Models.MatrixGroups.ON.rows1 CFSG.Models.MatrixGroups.ON.rows2 initial
    row_return_two row_nonreturn_one hn

theorem even_card (hn : ¬IsMulCommutative Model) : Even (Nat.card Model) :=
  MatrixModelSelectedRowPeriodTwo.even_card_of_row_period_two 3 154
    CFSG.Models.MatrixGroups.ON.rows1 CFSG.Models.MatrixGroups.ON.rows2 initial
    row_return_two row_nonreturn_one hn

end SymmetricSubgroupAsymptotics.CFSGONSelectedRowBasisSwap
