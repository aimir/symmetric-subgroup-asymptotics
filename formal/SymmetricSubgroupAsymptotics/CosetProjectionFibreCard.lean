import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite

/-! Fibres of the actual coset projection G/H→G/B. No normality or
split extension is required; the product equivalence is only a set chart. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CosetProjectionFibreCard
variable {G : Type*} [Group G]

def fibreEquiv (H B : Subgroup G) (h : H ≤ B) (q : G ⧸ B) :
    {x : G ⧸ H // Subgroup.quotientMapOfLE h x=q} ≃ B ⧸ H.subgroupOf B := by
  let e := Subgroup.quotientEquivProdOfLE h
  have hfst (x : G ⧸ H) : (e x).1=Subgroup.quotientMapOfLE h x := rfl
  refine
    { toFun := fun x => (e x.val).2
      invFun := fun z => ⟨e.symm (q,z),?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [←hfst,e.apply_symm_apply]
  · intro x
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · exact x.property.symm
    · rfl
  · intro z
    exact congrArg Prod.snd (e.apply_symm_apply (q,z))

theorem card_fibre (H B : Subgroup G) (h : H ≤ B) (q : G ⧸ B) :
    Nat.card {x : G ⧸ H // Subgroup.quotientMapOfLE h x=q} =
      (H.subgroupOf B).index := by
  exact (Nat.card_congr (fibreEquiv H B h q)).trans (Subgroup.index_eq_card _).symm

end SymmetricSubgroupAsymptotics.CosetProjectionFibreCard
