import SymmetricSubgroupAsymptotics.PermutationBinaryFourAugmentation

/-! Expose the original coordinate sum using any installed finite-type
enumeration. The underlying univ sets agree, even when the finite-type
instances are not definitionally equal. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

theorem permutation_coordinateSum_apply
    {k X : Type} [Field k] [Finite X] [Fintype X] (v : X → k) :
    PermutationAugmentation.coordinateSum k X v=∑ x : X,v x := by
  unfold PermutationAugmentation.coordinateSum
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_univ]
  · intro x _
    rfl

end SymmetricSubgroupAsymptotics
