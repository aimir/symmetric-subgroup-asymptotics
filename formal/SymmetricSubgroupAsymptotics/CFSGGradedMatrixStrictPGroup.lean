import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups
import Mathlib.Data.Fintype.Order
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.GroupTheory.PGroup

/-! Strictly raising matrices for an arbitrary finite integer grading
are nilpotent. Consequently the literal strict unit subgroup is a
p-group in characteristic p, including repeated grading weights. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixStrictPGroup
open CFSGGradedMatrixSubgroups
open scoped BigOperators
variable {I R : Type*} [Fintype I] [DecidableEq I] [Semiring R]

theorem pow_entry_eq_zero (w : I → ℤ) (M : Matrix I I R)
    (hM : ∀ i j, w i ≤ w j → M i j = 0) (k : ℕ) :
    ∀ i j, w i < w j+(k : ℤ) → (M^k) i j = 0 := by
  induction k with
  | zero =>
    intro i j hij
    have hne : i ≠ j := by intro he; subst j; omega
    simp only [pow_zero, Matrix.one_apply, if_neg hne]
  | succ k ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hil : w i < w l+(k : ℤ)
    · rw [ih i l hil, zero_mul]
    · rw [hM l j (by omega), mul_zero]

theorem isNilpotent_of_strict (w : I → ℤ) (M : Matrix I I R)
    (hM : ∀ i j, w i ≤ w j → M i j = 0) : IsNilpotent M := by
  obtain ⟨a,ha⟩ := Finite.bddBelow_range w
  obtain ⟨b,hb⟩ := Finite.bddAbove_range w
  let n := (b-a).toNat+1
  refine ⟨n, ?_⟩
  ext i j
  change (M^n) i j = 0
  apply pow_entry_eq_zero w M hM n
  have hi := hb (Set.mem_range_self i)
  have hj := ha (Set.mem_range_self j)
  have hn := Int.self_le_toNat (b-a)
  dsimp only [n]
  omega

noncomputable section
variable {K : Type*} [Field K]

theorem strictUnits_isPGroup (w : I → ℤ) (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPGroup p (strictUnits (K := K) w) := by
  rcases isEmpty_or_nonempty I with hI | hI
  · letI := hI
    intro A
    refine ⟨0, ?_⟩
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact isEmptyElim i
  · letI := hI
    intro A
    have hstrict : ∀ i j, w i ≤ w j →
        ((A.val : Matrix I I K)-1) i j = 0 := by
      intro i j hij
      rw [Matrix.sub_apply, A.property i j hij, sub_self]
    obtain ⟨n,hn⟩ := isNilpotent_of_strict w ((A.val : Matrix I I K)-1) hstrict
    have hnp : n ≤ p^n := Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_left (Fact.out : p.Prime).two_le n)
    have hpz : ((A.val : Matrix I I K)-1)^(p^n) = 0 := pow_eq_zero_of_le hnp hn
    have he := add_pow_char_pow_of_commute p n
      (Commute.one_right ((A.val : Matrix I I K)-1))
    rw [sub_add_cancel, one_pow, hpz, zero_add] at he
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact he

end
end SymmetricSubgroupAsymptotics.CFSGGradedMatrixStrictPGroup
