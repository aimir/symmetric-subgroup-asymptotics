import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.IntervalCases

/-! Every actual quotient of a permutation group on at most two points is
abelian. Thus the original degree of a nonabelian quotient exceeds two;
small physical factors can be put in the abelian block without a census. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SmallPermutationQuotient

theorem perm_comm {n : ℕ} (hn : n ≤ 2) (f g : Equiv.Perm (Fin n)) :
    f*g=g*f := by
  interval_cases n <;> revert f g <;> decide +kernel

theorem quotient_comm {n : ℕ} (hn : n ≤ 2)
    (G : Subgroup (Equiv.Perm (Fin n))) {Q : Type*} [Group Q]
    (q : G →* Q) (onto : Function.Surjective q) :
    ∀ x y : Q,x*y=y*x := by
  intro x y
  obtain ⟨u,rfl⟩ := onto x
  obtain ⟨v,rfl⟩ := onto y
  have h : u*v=v*u := Subtype.ext (perm_comm hn u.val v.val)
  simpa only [map_mul] using congrArg q h

theorem two_lt_degree {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    {Q : Type*} [Group Q] (q : G →* Q) (onto : Function.Surjective q)
    (hnon : ¬∀ x y : Q,x*y=y*x) : 2 < n := by
  by_contra h
  exact hnon (quotient_comm (by omega) G q onto)

end SymmetricSubgroupAsymptotics.SmallPermutationQuotient
