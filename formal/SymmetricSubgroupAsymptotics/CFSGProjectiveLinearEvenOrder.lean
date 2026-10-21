import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! A characteristic-independent even-order witness in actual PSL.
The block rotation has determinant one, fourth power one, and a nonzero
off-diagonal entry. It is not in the actual SL center, so its projective
image is a nonidentity element of order two or four. No Lie-group order
formula or model identification is used. The ring-level statement also
holds for infinite coefficient rings, where `Nat.card` is zero. -/
set_option autoImplicit false
noncomputable section
open scoped Classical MatrixGroups
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEvenOrder

def turn (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, -1; 1, 0]

theorem turn_det (R : Type*) [CommRing R] : (turn R).det = 1 := by
  simp [turn, Matrix.det_fin_two]

theorem turn_sq (R : Type*) [CommRing R] : (turn R) ^ 2 = -(1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [turn, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem turn_four (R : Type*) [CommRing R] : (turn R) ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by decide, pow_mul, turn_sq]
  simp

def blockTurn (R : Type*) [CommRing R] (m : ℕ) :
    Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) R :=
  Matrix.fromBlocks (turn R) 0 0 1

theorem blockTurn_det (R : Type*) [CommRing R] (m : ℕ) : (blockTurn R m).det = 1 := by
  rw [blockTurn, Matrix.det_fromBlocks_zero₂₁, turn_det, Matrix.det_one, mul_one]

theorem blockTurn_four (R : Type*) [CommRing R] (m : ℕ) : (blockTurn R m) ^ 4 = 1 := by
  rw [blockTurn, Matrix.fromBlocks_diagonal_pow, turn_four, one_pow, Matrix.fromBlocks_one]

def splitIndex (n : ℕ) (hn : 2 ≤ n) : Fin 2 ⊕ Fin (n - 2) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))

def rotation (R : Type*) [CommRing R] (n : ℕ) (hn : 2 ≤ n) :
    Matrix.SpecialLinearGroup (Fin n) R :=
  ⟨Matrix.reindex (splitIndex n hn) (splitIndex n hn) (blockTurn R (n - 2)), by
    rw [Matrix.det_reindex_self, blockTurn_det]⟩

theorem rotation_four (R : Type*) [CommRing R] (n : ℕ) (hn : 2 ≤ n) :
    rotation R n hn ^ 4 = 1 := by
  apply Subtype.ext
  change (Matrix.reindexAlgEquiv R R (splitIndex n hn) (blockTurn R (n - 2))) ^ 4 = 1
  rw [← map_pow, blockTurn_four, map_one]

theorem rotation_not_center (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : 2 ≤ n) :
    rotation R n hn ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) R) := by
  intro hc
  let e := splitIndex n hn
  let i : Fin n := e (Sum.inl (0 : Fin 2))
  let j : Fin n := e (Sum.inl (1 : Fin 2))
  have hji : j ≠ i := by
    intro h
    have h' := e.injective h
    have hfin : (1 : Fin 2) = 0 := Sum.inl.inj h'
    exact (by decide : (1 : Fin 2) ≠ 0) hfin
  have hs := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hc i
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) R => M j i) hs
  have hleft : (Matrix.scalar (Fin n) (rotation R n hn i i)) j i = 0 := by
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hji]
  have hright : rotation R n hn j i = 1 := by
    change (Matrix.reindex e e (blockTurn R (n - 2)))
      (e (Sum.inl (1 : Fin 2))) (e (Sum.inl (0 : Fin 2))) = 1
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rfl
  change (Matrix.scalar (Fin n) (rotation R n hn i i)) j i = rotation R n hn j i at he
  rw [hleft, hright] at he
  exact zero_ne_one he

/-- Every nonidentity fourth-root of one forces an even `Nat.card`.
This uses its actual element order, including the possibility of order four. -/
theorem even_card_of_nontrivial_fourth_root {G : Type*} [Group G]
    (g : G) (hne : g ≠ 1) (hfour : g ^ 4 = 1) : Even (Nat.card G) := by
  apply even_iff_two_dvd.mpr
  apply dvd_trans ?_ (orderOf_dvd_natCard g)
  have hd : orderOf g ∣ 2 ^ 2 := by
    simpa only [show (2 : ℕ) ^ 2 = 4 by decide] using orderOf_dvd_of_pow_eq_one hfour
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  cases k with
  | zero =>
    exfalso
    apply hne
    apply orderOf_eq_one_iff.mp
    simpa only [pow_zero] using hk
  | succ k =>
    rw [hk, pow_succ]
    exact ⟨2 ^ k, mul_comm _ _⟩

theorem projectiveSpecialLinear_even_card (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : 2 ≤ n) :
    Even (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin n) R)) := by
  let q : Matrix.SpecialLinearGroup (Fin n) R →*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) R := QuotientGroup.mk' _
  apply even_card_of_nontrivial_fourth_root (q (rotation R n hn))
  · intro h
    exact rotation_not_center R n hn ((QuotientGroup.eq_one_iff _).mp h)
  · rw [← map_pow, rotation_four, map_one]

theorem typeA_even_card (r : ℕ) (q : CFSG.PrimePower) (hr : 1 ≤ r) :
    Even (Nat.card (CFSG.Models.A r q)) :=
  projectiveSpecialLinear_even_card q.Field (r + 1) (by omega)

end SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEvenOrder
