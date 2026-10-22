import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Finite.Card

/-! Forward preservation of a binary relation by a finite permutation
already implies preservation in both directions. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGFinitePermutationRelation
variable {J : Type*} [Finite J]

theorem relation_iff_of_forward (R : J→J→Prop) (σ : Equiv.Perm J)
    (hσ : ∀i j,R i j→R (σ i) (σ j)) (i j : J) : R (σ i) (σ j)↔R i j := by
  classical
  constructor
  · intro h
    let T := {x : J×J // R x.1 x.2}
    let f : T→T := fun x=>⟨(σ x.val.1,σ x.val.2),hσ _ _ x.property⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Prod.ext
      · exact σ.injective (congrArg (fun z : T=>z.val.1) hxy)
      · exact σ.injective (congrArg (fun z : T=>z.val.2) hxy)
    obtain ⟨x,hx⟩ := Finite.surjective_of_injective hf (⟨(σ i,σ j),h⟩ : T)
    have hxi : x.val.1=i := σ.injective (congrArg (fun z : T=>z.val.1) hx)
    have hxj : x.val.2=j := σ.injective (congrArg (fun z : T=>z.val.2) hx)
    simpa only [hxi,hxj] using x.property
  · exact hσ i j

end SymmetricSubgroupAsymptotics.CFSGFinitePermutationRelation
