import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.Perm.Basic

/-! An explicit permutation sends one ordered distinct pair to another.
Only two literal swaps are used; no finite permutation census is needed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairPermutation
variable {I : Type*} [DecidableEq I]

def pairPermutation (a b c d : I) : Equiv.Perm I :=
  Equiv.swap (Equiv.swap a c b) d * Equiv.swap a c

theorem pairPermutation_first (a b c d : I) (hab : a ≠ b) (hcd : c ≠ d) :
    pairPermutation a b c d a = c := by
  have hcb : c ≠ Equiv.swap a c b := by
    intro he
    apply hab
    apply (Equiv.swap a c).injective
    exact (Equiv.swap_apply_left a c).trans he
  unfold pairPermutation
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hcb hcd]

theorem pairPermutation_second (a b c d : I) : pairPermutation a b c d b = d := by
  unfold pairPermutation
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairPermutation
