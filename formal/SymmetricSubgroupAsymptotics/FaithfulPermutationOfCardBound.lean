import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

/-! A small actual finite quotient has a literal padded regular action.
The quotient itself, rather than its original parent group, is embedded. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FaithfulPermutationOfCardBound

theorem exists_action {G : Type} [Group G] [Finite G] (n : ℕ)
    (hcard : Nat.card G≤n) :
    ∃ f : G →* Equiv.Perm (Fin n), Function.Injective f := by
  letI : Fintype G := Fintype.ofFinite G
  have he : Nonempty (G ↪ Fin n) := Function.Embedding.nonempty_of_card_le (by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using hcard)
  let e := Classical.choice he
  refine ⟨(Equiv.Perm.viaEmbeddingHom e).comp (MulAction.toPermHom G G),?_⟩
  exact (Equiv.Perm.viaEmbeddingHom_injective e).comp MulAction.toPerm_injective

end SymmetricSubgroupAsymptotics.FaithfulPermutationOfCardBound
