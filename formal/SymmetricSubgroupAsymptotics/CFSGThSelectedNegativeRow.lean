import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Th
import SymmetricSubgroupAsymptotics.MatrixModelSelectedRowPeriodTwo
import Mathlib.Tactic.FinCases

/-! ONE selected negative eigenROW14 in the first pinned Th matrix.
Thirty-one fixed blocks of eight coefficients certify exactly248 entries.
No column, whole-matrix square, inverse, group order or selected scalar
dot product is asserted. Source SHAa1e148b037866e8b1d2f66f3cc9eab494853ee9e9de78c21fd10a9830b3a5d01.
Abstract row linearity gives period2; the checked contragredient bridge
then gives even order under inherited noncommutativity only.
No resource option is raised. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGThSelectedNegativeRow

abbrev Model := CFSG.Models.MatrixGroups.Th.Model
abbrev V := Fin 248 → ZMod 3

def a : Matrix (Fin 248) (Fin 248) (ZMod 3) :=
  CFSG.Models.MatrixData.matrix 3 248 CFSG.Models.MatrixGroups.Th.rows1

def initial : V := Pi.single (14 : Fin 248) 1

def positionAt (b : Fin 31) (j : Fin 8) : Fin 248 :=
  Fin.ofNat 248 (8 * b.val + j.val)

def rowEntryAt (j : Fin 248) : Prop :=
  a (14 : Fin 248) j = ((2 : ZMod 3) • initial) j

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

theorem block14 : ∀ j : Fin 8, rowEntryAt (positionAt 14 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block15 : ∀ j : Fin 8, rowEntryAt (positionAt 15 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block16 : ∀ j : Fin 8, rowEntryAt (positionAt 16 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block17 : ∀ j : Fin 8, rowEntryAt (positionAt 17 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block18 : ∀ j : Fin 8, rowEntryAt (positionAt 18 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block19 : ∀ j : Fin 8, rowEntryAt (positionAt 19 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block20 : ∀ j : Fin 8, rowEntryAt (positionAt 20 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block21 : ∀ j : Fin 8, rowEntryAt (positionAt 21 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block22 : ∀ j : Fin 8, rowEntryAt (positionAt 22 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block23 : ∀ j : Fin 8, rowEntryAt (positionAt 23 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block24 : ∀ j : Fin 8, rowEntryAt (positionAt 24 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block25 : ∀ j : Fin 8, rowEntryAt (positionAt 25 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block26 : ∀ j : Fin 8, rowEntryAt (positionAt 26 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block27 : ∀ j : Fin 8, rowEntryAt (positionAt 27 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block28 : ∀ j : Fin 8, rowEntryAt (positionAt 28 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block29 : ∀ j : Fin 8, rowEntryAt (positionAt 29 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block30 : ∀ j : Fin 8, rowEntryAt (positionAt 30 j) := by
  unfold rowEntryAt
  decide +kernel

theorem block_entries (b : Fin 31) (j : Fin 8) : rowEntryAt (positionAt b j) := by
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
  · exact block20 j
  · exact block21 j
  · exact block22 j
  · exact block23 j
  · exact block24 j
  · exact block25 j
  · exact block26 j
  · exact block27 j
  · exact block28 j
  · exact block29 j
  · exact block30 j

theorem selected_row (j : Fin 248) :
    a (14 : Fin 248) j = ((2 : ZMod 3) • initial) j := by
  let b : Fin 31 := ⟨j.val / 8,by omega⟩
  let k : Fin 8 := ⟨j.val % 8,Nat.mod_lt _ (by decide)⟩
  have hj : positionAt b k = j := by
    apply Fin.ext
    change (8 * (j.val / 8) + j.val % 8) % 248 = j.val
    have he : 8 * (j.val / 8) + j.val % 8 = j.val := by omega
    rw [he,Nat.mod_eq_of_lt j.isLt]
  change rowEntryAt j
  rw [←hj]
  exact block_entries b k

private theorem basis_vecMul_of_row {n : ℕ} {R : Type*} [Semiring R]
    (A : Matrix (Fin n) (Fin n) R) (i : Fin n) (v : Fin n → R)
    (h : ∀ j, A i j = v j) : Pi.single i 1 ᵥ* A = v := by
  rw [Matrix.single_one_vecMul]
  exact funext h

private theorem row_period_two_of_eigen {n : ℕ} {R : Type*} [Semiring R]
    (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (c : R)
    (hc : c*c = 1) (hv : v ᵥ* A = c • v) : (v ᵥ* A) ᵥ* A = v := by
  rw [hv,Matrix.smul_vecMul,hv,smul_smul,hc,one_smul]

theorem row_eigenvalue : initial ᵥ* a = (2 : ZMod 3) • initial :=
  basis_vecMul_of_row a 14 ((2 : ZMod 3) • initial) selected_row

theorem row_return_two : (initial ᵥ* a) ᵥ* a = initial :=
  row_period_two_of_eigen a initial (2 : ZMod 3) (by decide +kernel) row_eigenvalue

theorem row_nonreturn_one : initial ᵥ* a ≠ initial := by
  have hne : ((2 : ZMod 3) • initial) (14 : Fin 248) ≠ initial 14 := by decide +kernel
  intro h
  exact hne (congrFun (row_eigenvalue.symm.trans h) (14 : Fin 248))

theorem exists_two_dvd_orderOf (hn : ¬IsMulCommutative Model) :
    ∃ g : Model, 2 ∣ orderOf g :=
  MatrixModelSelectedRowPeriodTwo.exists_two_dvd_orderOf 3 248
    CFSG.Models.MatrixGroups.Th.rows1 CFSG.Models.MatrixGroups.Th.rows2 initial
    row_return_two row_nonreturn_one hn

theorem even_card (hn : ¬IsMulCommutative Model) : Even (Nat.card Model) :=
  MatrixModelSelectedRowPeriodTwo.even_card_of_row_period_two 3 248
    CFSG.Models.MatrixGroups.Th.rows1 CFSG.Models.MatrixGroups.Th.rows2 initial
    row_return_two row_nonreturn_one hn

end SymmetricSubgroupAsymptotics.CFSGThSelectedNegativeRow
