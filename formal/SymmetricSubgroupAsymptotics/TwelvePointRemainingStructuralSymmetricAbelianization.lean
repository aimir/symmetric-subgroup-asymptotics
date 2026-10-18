import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricTop

/-! The literal four-letter symmetric top has abelianization of order
at most two. The finite witness tests only individual even permutations
as single commutators; it does not enumerate subgroups or normal states. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural

theorem alternating_le_symmetric_commutator :
    alternatingGroup (Fin 4) ≤ commutator (Equiv.Perm (Fin 4)) := by
  have witness : ∀ g : Equiv.Perm (Fin 4), Equiv.Perm.sign g=1 →
      ∃ a b : Equiv.Perm (Fin 4), ∀ i : Fin 4, ⁅a,b⁆ i=g i := by decide +kernel
  intro g hg
  obtain ⟨a,b,hab⟩ := witness g hg
  have he : ⁅a,b⁆=g := Equiv.ext hab
  rw [← he]
  exact Subgroup.commutator_mem_commutator
    (show a ∈ (⊤ : Subgroup (Equiv.Perm (Fin 4))) from trivial)
    (show b ∈ (⊤ : Subgroup (Equiv.Perm (Fin 4))) from trivial)

theorem symmetric_abelianization_card_le_two :
    Nat.card (Equiv.Perm (Fin 4) ⧸ commutator (Equiv.Perm (Fin 4))) ≤ 2 := by
  have hd : (commutator (Equiv.Perm (Fin 4))).index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using
      Subgroup.index_dvd_of_le alternating_le_symmetric_commutator
  change (commutator (Equiv.Perm (Fin 4))).index ≤ 2
  exact Nat.le_of_dvd (by decide : 0 < 2) hd

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
