import SymmetricSubgroupAsymptotics.CFSGAlternatingStarReconstruction
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Equality of automorphisms from the actual oriented star generators. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingStarAutomorphismExt
open Equiv Equiv.Perm CFSGAlternatingStarGenerators CFSGAlternatingThreeCycleStars
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem hom_ext_of_star {M : Type*} [Group M]
    (f g : alternatingGroup α→*M) (a b : α) (hab : a≠b)
    (h : ∀ i (hia : i≠a) (hib : i≠b),
      f ⟨cycle a b i,(cycle_isThreeCycle a b i hab (Ne.symm hia) (Ne.symm hib)).mem_alternatingGroup⟩=
      g ⟨cycle a b i,(cycle_isThreeCycle a b i hab (Ne.symm hia) (Ne.symm hib)).mem_alternatingGroup⟩) : f=g := by
  let R : Subgroup (alternatingGroup α) := f.eqLocus g
  have hr : alternatingGroup α≤R.map (alternatingGroup α).subtype := by
    apply alternating_le_of_star _ a b hab
    intro i hia hib
    refine ⟨⟨cycle a b i,(cycle_isThreeCycle a b i hab (Ne.symm hia) (Ne.symm hib)).mem_alternatingGroup⟩,?_,rfl⟩
    exact h i hia hib
  apply MonoidHom.ext
  intro x
  obtain ⟨y,hy,he⟩ := hr x.property
  have he' : y=x := Subtype.ext he
  subst y
  exact hy

end SymmetricSubgroupAsymptotics.CFSGAlternatingStarAutomorphismExt
