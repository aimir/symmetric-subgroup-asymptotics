import Mathlib.Logic.Equiv.Basic

/-! For a permutation-invariant family of coordinate functions, a
single collision between distinct coordinate evaluations forces every
function to be constant. Thus a nonconstant actual sign code separates
all coordinate characters. No list of invariant codes is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PermutationInvariantCoordinateSeparation

variable {I K : Type*} (C : Set (I → K))
    (hperm : ∀ (s : Equiv.Perm I) (v : I → K),v∈C → v ∘ s∈C)

include hperm in
theorem constant_of_coordinate_collision
    (i j : I) (hne : i≠j)
    (he : ∀ (v : I → K),v∈C → v i=v j) :
    ∀ (v : I → K),v∈C → ∀ k l,v k=v l := by
  intro v hv
  have hk : ∀ k,v i=v k := by
    intro k
    by_cases hki : k=i
    · rw [hki]
    · have h := he (v ∘ Equiv.swap j k) (hperm (Equiv.swap j k) v hv)
      change v (Equiv.swap j k i)=v (Equiv.swap j k j) at h
      simpa only [Equiv.swap_apply_of_ne_of_ne hne (Ne.symm hki),
        Equiv.swap_apply_left] using h
  intro k l
  exact (hk k).symm.trans (hk l)

include hperm in
theorem coordinate_evaluations_injective_of_not_constant
    (hnot : ¬∀ (v : I → K),v∈C → ∀ i j,v i=v j) :
    Function.Injective (fun i : I => fun v : {v : I → K // v∈C} => v.val i) := by
  intro i j he
  by_contra hne
  apply hnot
  exact constant_of_coordinate_collision C hperm i j hne
    (fun v hv => congrFun he ⟨v,hv⟩)

end SymmetricSubgroupAsymptotics.PermutationInvariantCoordinateSeparation
