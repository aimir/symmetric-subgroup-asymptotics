import Mathlib.Data.Fintype.Order
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Pointwise comparison of two permutations of a finite linear order
forces equality. This supplies the final combinatorial step in block
Bruhat uniqueness without assuming one-dimensional blocks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFinitePermutationOrder
variable {L : Type*} [Fintype L] [LinearOrder L]

theorem eq_of_pointwise_le (phi psi : Equiv.Perm L) (h : ∀ l, phi l ≤ psi l) : phi = psi := by
  let e : L ≃o Fin (Fintype.card L) := (Fintype.orderIsoFinOfCardEq L rfl).symm
  have he : (∑ l : L, (e (phi l)).val) = ∑ l : L, (e (psi l)).val :=
    (Equiv.sum_comp phi (fun l => (e l).val)).trans (Equiv.sum_comp psi (fun l => (e l).val)).symm
  apply Equiv.ext
  intro l
  apply e.injective
  apply Fin.ext
  have hle (i : L) : (e (phi i)).val ≤ (e (psi i)).val := e.monotone (h i)
  by_contra hn
  have hlt : (e (phi l)).val < (e (psi l)).val := lt_of_le_of_ne (hle l) hn
  have hs : (∑ i : L, (e (phi i)).val) < ∑ i : L, (e (psi i)).val :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨l, Finset.mem_univ l, hlt⟩
  exact (ne_of_lt hs) he

end SymmetricSubgroupAsymptotics.CFSGFinitePermutationOrder
