import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Ly
import SymmetricSubgroupAsymptotics.MatrixModelSelectedRowPeriodTwo
import Mathlib.Tactic.FinCases

/-! ONE fixed row combination for the first pinned Ly matrix over F5.
The selected row is e0+2e55. Fourteen fixed eight-position blocks certify
its right image is4 times itself, using only coefficients in rows0/55.
No column, matrix square, inverse, order certificate or vector search.
Source SHA8c654477c2e3244de5eed0d9d3157c207292b354230366a975801bfe91b94d0f.
All finite claims below are kernel obligations; no resource option rises. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGLySelectedRowCombination

abbrev Model := CFSG.Models.MatrixGroups.Ly.Model
abbrev V := Fin 111 → ZMod 5

def a : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  CFSG.Models.MatrixData.matrix 5 111 CFSG.Models.MatrixGroups.Ly.rows1

def initial : V :=
  Pi.single (0 : Fin 111) 1 + (2 : ZMod 5) • Pi.single (55 : Fin 111) 1

def positionAt (b : Fin 14) (j : Fin 8) : Fin 111 :=
  Fin.ofNat 111 (8 * b.val + j.val)

def rowEntryAt (j : Fin 111) : Prop :=
  a (0 : Fin 111) j + (2 : ZMod 5) * a (55 : Fin 111) j =
    ((4 : ZMod 5) • initial) j

theorem block00 : ∀ j : Fin 8, rowEntryAt (positionAt 0 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block01 : ∀ j : Fin 8, rowEntryAt (positionAt 1 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block02 : ∀ j : Fin 8, rowEntryAt (positionAt 2 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block03 : ∀ j : Fin 8, rowEntryAt (positionAt 3 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block04 : ∀ j : Fin 8, rowEntryAt (positionAt 4 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block05 : ∀ j : Fin 8, rowEntryAt (positionAt 5 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block06 : ∀ j : Fin 8, rowEntryAt (positionAt 6 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block07 : ∀ j : Fin 8, rowEntryAt (positionAt 7 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block08 : ∀ j : Fin 8, rowEntryAt (positionAt 8 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block09 : ∀ j : Fin 8, rowEntryAt (positionAt 9 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block10 : ∀ j : Fin 8, rowEntryAt (positionAt 10 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block11 : ∀ j : Fin 8, rowEntryAt (positionAt 11 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block12 : ∀ j : Fin 8, rowEntryAt (positionAt 12 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block13 : ∀ j : Fin 8, rowEntryAt (positionAt 13 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block_entries (b : Fin 14) (j : Fin 8) : rowEntryAt (positionAt b j) := by
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

theorem selected_combination (j : Fin 111) :
    a (0 : Fin 111) j + (2 : ZMod 5) * a (55 : Fin 111) j =
      ((4 : ZMod 5) • initial) j := by
  let b : Fin 14 := ⟨j.val / 8,by omega⟩
  let k : Fin 8 := ⟨j.val % 8,Nat.mod_lt _ (by decide)⟩
  have hj : positionAt b k = j := by
    apply Fin.ext
    change (8 * (j.val / 8) + j.val % 8) % 111 = j.val
    have he : 8 * (j.val / 8) + j.val % 8 = j.val := by omega
    rw [he,Nat.mod_eq_of_lt j.isLt]
  change rowEntryAt j
  rw [←hj]
  exact block_entries b k

private theorem basis_pair_vecMul_of_coeff {n : ℕ} {R : Type*} [Semiring R]
    (A : Matrix (Fin n) (Fin n) R) (i k : Fin n) (c : R) (v : Fin n → R)
    (h : ∀ j, A i j + c * A k j = v j) :
    (Pi.single i 1 + c • Pi.single k 1) ᵥ* A = v := by
  rw [Matrix.add_vecMul,Matrix.smul_vecMul,
    Matrix.single_one_vecMul,Matrix.single_one_vecMul]
  exact funext h

private theorem row_period_two_of_eigen {n : ℕ} {R : Type*} [Semiring R]
    (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (c : R)
    (hc : c*c = 1) (hv : v ᵥ* A = c • v) : (v ᵥ* A) ᵥ* A = v := by
  rw [hv,Matrix.smul_vecMul,hv,smul_smul,hc,one_smul]

theorem row_eigenvalue : initial ᵥ* a = (4 : ZMod 5) • initial :=
  basis_pair_vecMul_of_coeff a 0 55 (2 : ZMod 5)
    ((4 : ZMod 5) • initial) selected_combination

theorem row_return_two : (initial ᵥ* a) ᵥ* a = initial :=
  row_period_two_of_eigen a initial (4 : ZMod 5) (by decide +kernel) row_eigenvalue

theorem row_nonreturn_one : initial ᵥ* a ≠ initial := by
  have hne : ((4 : ZMod 5) • initial) (0 : Fin 111) ≠ initial 0 := by decide +kernel
  intro h
  exact hne (congrFun (row_eigenvalue.symm.trans h) (0 : Fin 111))

theorem exists_two_dvd_orderOf (hn : ¬IsMulCommutative Model) :
    ∃ g : Model, 2 ∣ orderOf g :=
  MatrixModelSelectedRowPeriodTwo.exists_two_dvd_orderOf 5 111
    CFSG.Models.MatrixGroups.Ly.rows1 CFSG.Models.MatrixGroups.Ly.rows2 initial
    row_return_two row_nonreturn_one hn

theorem even_card (hn : ¬IsMulCommutative Model) : Even (Nat.card Model) :=
  MatrixModelSelectedRowPeriodTwo.even_card_of_row_period_two 5 111
    CFSG.Models.MatrixGroups.Ly.rows1 CFSG.Models.MatrixGroups.Ly.rows2 initial
    row_return_two row_nonreturn_one hn

end SymmetricSubgroupAsymptotics.CFSGLySelectedRowCombination
