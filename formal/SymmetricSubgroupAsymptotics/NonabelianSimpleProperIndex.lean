import SymmetricSubgroupAsymptotics.LinearThreeSolvable
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Data.Fintype.EquivFin

/-! A nonabelian finite simple group has no proper subgroup of index below five.
The proof uses its faithful coset action and the internally proved solvability of S₄.
No classification or published index estimate is assumed. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Every proper subgroup of a finite nonabelian simple group has index at least five. -/
theorem nonabelianSimple_proper_index_five_le
    {T : Type*} [Group T] [Finite T] [IsSimpleGroup T]
    (hnoncomm : ¬ ∀ a b : T, a * b = b * a)
    (H : Subgroup T) (hH : H ≠ ⊤) : 5 ≤ H.index := by
  classical
  by_contra hindex
  have hsmall : H.index ≤ 4 := by omega
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore H.normalCore_normal with h | h
    · exact h
    · exact False.elim (hH (top_le_iff.mp (h ▸ H.normalCore_le)))
  let f : T →* Equiv.Perm (T ⧸ H) := MulAction.toPermHom T (T ⧸ H)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    exact (Subgroup.normalCore_eq_ker H).symm.trans hcore
  letI : Fintype (T ⧸ H) := Fintype.ofFinite _
  have hcard : Fintype.card (T ⧸ H) ≤ Fintype.card (Fin 4) := by
    simpa only [Fintype.card_fin, ← Nat.card_eq_fintype_card,
      ← Subgroup.index_eq_card, Nat.card_fin] using hsmall
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  letI : IsSolvable (Equiv.Perm (Fin 4)) := naturalS4_isSolvable
  letI : IsSolvable (Equiv.Perm (T ⧸ H)) :=
    solvable_of_solvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  have hsol : IsSolvable T := solvable_of_solvable_injective hf
  exact hnoncomm (IsSimpleGroup.comm_iff_isSolvable.mpr hsol)

/-- The witness half of a least-proper-index specification already implies the bound. -/
theorem nonabelianSimple_leastProperIndex_five_le
    {T : Type*} [Group T] [Finite T] [IsSimpleGroup T]
    (hnoncomm : ¬ ∀ a b : T, a * b = b * a) {ell : ℕ}
    (hwitness : ∃ H : Subgroup T, H ≠ ⊤ ∧ H.index = ell) : 5 ≤ ell := by
  obtain ⟨H, hH, hindex⟩ := hwitness
  simpa only [hindex] using nonabelianSimple_proper_index_five_le hnoncomm H hH

end SymmetricSubgroupAsymptotics
