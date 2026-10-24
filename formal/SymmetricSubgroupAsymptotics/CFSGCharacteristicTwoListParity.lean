import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Basic

/-! Computable finite parity certificates determine characteristic-two
list sums. The finite data involve only list counts, never a classical
polynomial-ring multiplication implementation. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCharacteristicTwoListParity
variable {I K : Type*} [DecidableEq I] [CommRing K] [CharP K 2]

theorem sum_map_eq_count_mod_two (l : List I) (f : I→K) :
    (l.map f).sum=∑e ∈ l.toFinset,((l.count e%2 : ℕ) : K)*f e := by
  rw [Finset.sum_list_map_count]
  apply Finset.sum_congr rfl
  intro e _
  rw [nsmul_eq_mul,CharP.natCast_eq_natCast_mod K 2]

private theorem sum_count_extend (l : List I) (f : I→K) (s : Finset I)
    (hl : l.toFinset⊆s) :
    (∑e ∈ l.toFinset,((l.count e%2 : ℕ) : K)*f e)=
      ∑e ∈ s,((l.count e%2 : ℕ) : K)*f e := by
  apply Finset.sum_subset hl
  intro e _ he
  have hn : e∉l := fun hm=>he (List.mem_toFinset.mpr hm)
  simp only [List.count_eq_zero_of_not_mem hn,Nat.zero_mod,Nat.cast_zero,zero_mul]

theorem sum_map_eq_of_count_mod_two (l r : List I) (f : I→K)
    (h : ∀e ∈ l.toFinset∪r.toFinset,l.count e%2=r.count e%2) :
    (l.map f).sum=(r.map f).sum := by
  rw [sum_map_eq_count_mod_two,sum_map_eq_count_mod_two]
  calc
    _=∑e ∈ l.toFinset∪r.toFinset,((l.count e%2 : ℕ) : K)*f e :=
      sum_count_extend l f _ Finset.subset_union_left
    _=∑e ∈ l.toFinset∪r.toFinset,((r.count e%2 : ℕ) : K)*f e := by
      apply Finset.sum_congr rfl
      intro e he
      rw [h e he]
    _=_ := (sum_count_extend r f _ Finset.subset_union_right).symm

end SymmetricSubgroupAsymptotics.CFSGCharacteristicTwoListParity
