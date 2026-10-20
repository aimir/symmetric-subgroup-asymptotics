import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators

/-! Actual finite module-generating sets convert to a common padded tuple
length without changing the original carrier or coefficient ring. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ModuleGeneratedBy

variable {R M : Type} [Semiring R] [AddCommMonoid M] [Module R M]

theorem of_finset_card_le (S : Finset M)
    (hS : Submodule.span R (S : Set M)=⊤) (n : ℕ) (hn : S.card≤n) :
    ModuleGeneratedBy R M n := by
  let e := S.equivFin
  let v : Fin n → M := fun i =>
    if hi : i.val<S.card then (e.symm ⟨i.val,hi⟩).val else 0
  refine ⟨v,top_unique ?_⟩
  rw [←hS]
  apply Submodule.span_mono
  intro x hx
  let a : Fin S.card := e ⟨x,hx⟩
  refine ⟨⟨a.val,Nat.lt_of_lt_of_le a.isLt hn⟩,?_⟩
  dsimp only [v]
  rw [dif_pos a.isLt]
  change (e.symm (e ⟨x,hx⟩)).val=x
  rw [Equiv.symm_apply_apply]

end SymmetricSubgroupAsymptotics.ModuleGeneratedBy
