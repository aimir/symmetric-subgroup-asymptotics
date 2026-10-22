import SymmetricSubgroupAsymptotics.CFSGPermutationSubsetProduct
import Mathlib.GroupTheory.Perm.MaximalSubgroups

/-! The split embedding's pure first coordinate is the literal extension
by the identity, hence stabilizes the original subset. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGPermutationSubsetProduct
open Equiv
variable {X : Type*} [DecidableEq X] (s : Set X)

theorem splitEmbedding_fst_eq_ofSubtype (a : Perm s) :
    splitEmbedding s (a, 1) = Perm.ofSubtype a := by
  apply Perm.ext
  intro x
  by_cases hx : x ∈ s
  · rw [splitEmbedding_apply_mem s a 1 hx, Perm.ofSubtype_apply_of_mem a hx]
  · rw [splitEmbedding_apply_notMem s a 1 hx, Perm.ofSubtype_apply_of_not_mem a hx]
    rfl

theorem splitEmbedding_fst_mem_stabilizer (a : Perm s) :
    splitEmbedding s (a, 1) ∈ MulAction.stabilizer (Perm X) s := by
  rw [splitEmbedding_fst_eq_ofSubtype]
  exact Perm.ofSubtype_mem_stabilizer a

end SymmetricSubgroupAsymptotics.CFSGPermutationSubsetProduct
