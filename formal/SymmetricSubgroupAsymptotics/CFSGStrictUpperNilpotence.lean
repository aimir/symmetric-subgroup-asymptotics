import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Nilpotent.Basic
import Lean.Elab.Tactic.Omega

/-! Symbolic nilpotence and defining-characteristic order for actual
upper unitriangular matrices. There is no finite matrix enumeration. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGStrictUpperNilpotence
open Matrix
variable {R : Type*} [Semiring R] {n : ℕ}

/-- A product of k strictly upper triangular factors can only move an
entry at least k positions to the right. -/
theorem pow_entry_eq_zero (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j : Fin n,j ≤ i → A i j=0) (k : ℕ) :
    ∀ i j : Fin n,j.val < i.val+k → (A^k) i j=0 := by
  induction k with
  | zero =>
    intro i j hij
    have hne : i≠j := by intro h;subst j;omega
    simp only [pow_zero,Matrix.one_apply,if_neg hne]
  | succ k ih =>
    intro i j hij
    rw [pow_succ,Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hli : l.val < i.val+k
    · rw [ih i l hli,zero_mul]
    · have hjl : j ≤ l := by change j.val ≤ l.val;omega
      rw [hA l j hjl,mul_zero]

theorem pow_dimension_eq_zero (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j : Fin n,j ≤ i → A i j=0) : A^n=0 := by
  ext i j
  exact pow_entry_eq_zero A hA n i j (by have := j.isLt;omega)

theorem unitriangular_sub_one_pow_eq_zero {F : Type*} [Ring F]
    (A : Matrix (Fin n) (Fin n) F) (hA : A.BlockTriangular id)
    (hdiag : ∀ i,A i i=1) : (A-1)^n=0 := by
  apply pow_dimension_eq_zero
  intro i j hji
  by_cases he : j=i
  · subst j
    simp only [Matrix.sub_apply,hdiag,Matrix.one_apply_eq,sub_self]
  · have hlt : j < i := lt_of_le_of_ne hji he
    simp only [Matrix.sub_apply,hA hlt,Matrix.one_apply,if_neg (Ne.symm he),sub_zero]

/-- Every actual unitriangular matrix has p-power order in characteristic
p; dimension n itself is a sufficient exponent on p. -/
theorem unitriangular_pow_prime_pow {F : Type*} [Ring F] {p : ℕ}
    [Fact p.Prime] [CharP F p] [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) F) (hA : A.BlockTriangular id)
    (hdiag : ∀ i,A i i=1) : A^(p^n)=1 := by
  have hz : (A-1)^n=0 := unitriangular_sub_one_pow_eq_zero A hA hdiag
  have hn2 : n ≤ 2^n := Nat.lt_two_pow_self.le
  have hn : n ≤ p^n := hn2.trans
    (Nat.pow_le_pow_left (Fact.out : p.Prime).two_le n)
  have hpz : (A-1)^(p^n)=0 := pow_eq_zero_of_le hn hz
  have he := add_pow_char_pow_of_commute p n (Commute.one_right (A-1))
  rw [sub_add_cancel,one_pow,hpz,zero_add] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGStrictUpperNilpotence
