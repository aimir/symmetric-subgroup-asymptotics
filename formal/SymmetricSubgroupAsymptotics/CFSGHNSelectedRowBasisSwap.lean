import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.HN
import SymmetricSubgroupAsymptotics.MatrixModelSelectedRowPeriodTwo
import Mathlib.Tactic.FinCases

/-! A selected ROW-basis swap for the FIRST pinned HN matrix over F5.
Only ROWS1 and2 are certified: their133 coefficients each must be
the other basis vector. Seventeen fixed blocks of eight coefficient pairs
are closed kernel obligations; the final three positions wrap to valid
rows. Division/remainder proves complete coverage. No dot product, inverse,
group order or alternate-vector search is involved.
Pinned HN source SHA74501a9a57d8b718a85322e2b1a34c74a3669987d0864e47d31dd87d942790ac.
No heartbeat, recursion or memory option is raised. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGHNSelectedRowBasisSwap

abbrev Model := CFSG.Models.MatrixGroups.HN.Model
abbrev V := Fin 133 → ZMod 5

def a : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  CFSG.Models.MatrixData.matrix 5 133 CFSG.Models.MatrixGroups.HN.rows1

def initial : V := Pi.single (1 : Fin 133) 1
def other : V := Pi.single (2 : Fin 133) 1

def rowAt (b : Fin 17) (j : Fin 8) : Fin 133 :=
  Fin.ofNat 133 (8 * b.val + j.val)

def rowPairAt (j : Fin 133) : Prop :=
  a (1 : Fin 133) j = other j ∧ a (2 : Fin 133) j = initial j

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

theorem block_pairs (b : Fin 17) (j : Fin 8) : rowPairAt (rowAt b j) := by
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

theorem row_pair (i : Fin 133) : rowPairAt i := by
  let b : Fin 17 := ⟨i.val / 8,by omega⟩
  let j : Fin 8 := ⟨i.val % 8,Nat.mod_lt _ (by decide)⟩
  have hi : rowAt b j = i := by
    apply Fin.ext
    change (8 * (i.val / 8) + i.val % 8) % 133 = i.val
    have he : 8 * (i.val / 8) + i.val % 8 = i.val := by omega
    rw [he,Nat.mod_eq_of_lt i.isLt]
  rw [←hi]
  exact block_pairs b j

theorem row_one : ∀ j : Fin 133, a (1 : Fin 133) j = other j :=
  fun j => (row_pair j).1

theorem row_two : ∀ j : Fin 133, a (2 : Fin 133) j = initial j :=
  fun j => (row_pair j).2

private theorem basis_vecMul_of_row {n : ℕ} {R : Type*} [Semiring R]
    (A : Matrix (Fin n) (Fin n) R) (i : Fin n) (v : Fin n → R)
    (h : ∀ j, A i j = v j) : Pi.single i 1 ᵥ* A = v := by
  rw [Matrix.single_one_vecMul]
  exact funext h

theorem first_row_basis_swap : initial ᵥ* a = other :=
  basis_vecMul_of_row a 1 other row_one

theorem second_row_basis_swap : other ᵥ* a = initial :=
  basis_vecMul_of_row a 2 initial row_two

theorem row_return_two : (initial ᵥ* a) ᵥ* a = initial := by
  rw [first_row_basis_swap,second_row_basis_swap]

theorem row_nonreturn_one : initial ᵥ* a ≠ initial := by
  have hne : other (1 : Fin 133) ≠ initial 1 := by decide +kernel
  intro h
  have ho : other = initial := first_row_basis_swap.symm.trans h
  exact hne (congrFun ho (1 : Fin 133))

theorem exists_two_dvd_orderOf (hn : ¬IsMulCommutative Model) :
    ∃ g : Model, 2 ∣ orderOf g :=
  MatrixModelSelectedRowPeriodTwo.exists_two_dvd_orderOf 5 133
    CFSG.Models.MatrixGroups.HN.rows1 CFSG.Models.MatrixGroups.HN.rows2 initial
    row_return_two row_nonreturn_one hn

theorem even_card (hn : ¬IsMulCommutative Model) : Even (Nat.card Model) :=
  MatrixModelSelectedRowPeriodTwo.even_card_of_row_period_two 5 133
    CFSG.Models.MatrixGroups.HN.rows1 CFSG.Models.MatrixGroups.HN.rows2 initial
    row_return_two row_nonreturn_one hn

end SymmetricSubgroupAsymptotics.CFSGHNSelectedRowBasisSwap
