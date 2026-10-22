import SymmetricSubgroupAsymptotics.CFSGPermutationSubsetProduct
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! Parity of the literal sum-complement split embedding. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGPermutationSubsetProduct
open Equiv Perm
variable {X : Type*} [Fintype X] [DecidableEq X] (s : Set X) [Fintype s] [Fintype (sᶜ : Set X)]

theorem sign_splitEmbedding (a : Perm s) (b : Perm (sᶜ : Set X)) :
    sign (splitEmbedding s (a, b)) = sign a * sign b := by
  change sign ((Equiv.sumCompl (fun x => x ∈ s)).permCongr (Equiv.sumCongr a b)) = _
  rw [sign_permCongr, sign_sumCongr]
  congr 1
  exact sign_eq_sign_of_equiv _ _ (Equiv.refl _) (fun _ => rfl)

end SymmetricSubgroupAsymptotics.CFSGPermutationSubsetProduct
