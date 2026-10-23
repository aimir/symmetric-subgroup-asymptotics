import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-! Counts and the literal additive degree of a three-letter operator
word. These finite identities keep later root-string proofs uniform
instead of enumerating all eighty-one length-four words. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGThreeLetterWordDegree

theorem count_sum_eq_length (w : List (Fin 3)) :
    w.count 0+w.count 1+w.count 2=w.length := by
  induction w with
  | nil=>rfl
  | cons i w ih=>
    fin_cases i <;> simp [List.count_cons] at * <;> omega

theorem sum_eq_count_smul {V : Type*} [AddCommGroup V]
    (a : Fin 3→V) (w : List (Fin 3)) :
    (w.map a).sum=(w.count 0:ℤ) • a 0+(w.count 1:ℤ) • a 1+(w.count 2:ℤ) • a 2 := by
  induction w with
  | nil=>simp only [List.map_nil,List.sum_nil,List.count_nil,Nat.cast_zero,zero_smul,zero_add]
  | cons i w ih=>
    rw [List.map_cons,List.sum_cons,ih]
    fin_cases i <;> simp [Nat.cast_add,add_smul,one_smul] <;> abel

end SymmetricSubgroupAsymptotics.CFSGThreeLetterWordDegree
