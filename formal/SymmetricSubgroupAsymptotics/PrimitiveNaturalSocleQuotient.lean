import SymmetricSubgroupAsymptotics.PrimitiveCompositionActualOrder
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-! Natural alternating/symmetric rows control every actual nontrivial
normal quotient directly. This transports the given group isomorphism and
the given normal subgroup; no abstract order recognition is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] [Finite G]

theorem quotient_card_le_two_of_alternating_equiv
    (n : ℕ) (hn : 5≤n) (e : G≃*alternatingGroup (Fin n))
    (E : Subgroup G) [E.Normal] (hE : E≠⊥) : Nat.card (G⧸E)≤2 := by
  letI : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
  letI : Nontrivial E := E.nontrivial_iff_ne_bot.mpr hE
  let K := E.map e.toMonoidHom
  letI : K.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  letI : Nontrivial K := (E.equivMapOfInjective e.toMonoidHom e.injective).injective.nontrivial
  have hk : K=⊤ := (Subgroup.Normal.eq_bot_or_eq_top (H := K) inferInstance).resolve_left
    (K.nontrivial_iff_ne_bot.mp inferInstance)
  calc
    Nat.card (G⧸E)=E.index := E.index_eq_card.symm
    _ = K.index := (E.index_map_equiv e).symm
    _ ≤ 2 := by rw [hk,Subgroup.index_top]; omega

theorem quotient_card_le_two_of_symmetric_equiv
    (n : ℕ) (hn : 5≤n) (e : G≃*Equiv.Perm (Fin n))
    (E : Subgroup G) [E.Normal] (hE : E≠⊥) : Nat.card (G⧸E)≤2 := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  letI : Nontrivial E := E.nontrivial_iff_ne_bot.mpr hE
  let K := E.map e.toMonoidHom
  letI : K.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  letI : Nontrivial K := (E.equivMapOfInjective e.toMonoidHom e.injective).injective.nontrivial
  have hle : alternatingGroup (Fin n)≤K :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simpa using hn) inferInstance
  calc
    Nat.card (G⧸E)=E.index := E.index_eq_card.symm
    _ = K.index := (E.index_map_equiv e).symm
    _ ≤ (alternatingGroup (Fin n)).index := Subgroup.index_antitone hle
    _ = 2 := alternatingGroup.index_eq_two

namespace PrimitiveCompositionCatalogueMatch
variable {X : Type} [Finite X] (M : PrimitiveCompositionCatalogueMatch G X)

/-- Both actual natural row kinds have every nontrivial normal quotient of
order at most two, independently of either finite socle locator. -/
theorem natural_quotient_card_le_two
    (hn : (primitiveCompositionBoundRow M.row).kind≠.orderBound)
    (E : Subgroup G) [E.Normal] (hE : E≠⊥) : Nat.card (G⧸E)≤2 := by
  have hf : 5≤Nat.card X := by
    have h := (primitiveCompositionBoundRow M.row).natural_degree hn
    rwa [M.degree_eq] at h
  cases hk : (primitiveCompositionBoundRow M.row).kind with
  | orderBound => exact (hn hk).elim
  | naturalAlternating =>
      obtain ⟨e⟩ := M.alternating_equiv hk
      exact quotient_card_le_two_of_alternating_equiv (Nat.card X) hf e E hE
  | naturalSymmetric =>
      obtain ⟨e⟩ := M.symmetric_equiv hk
      exact quotient_card_le_two_of_symmetric_equiv (Nat.card X) hf e E hE

end PrimitiveCompositionCatalogueMatch
end SymmetricSubgroupAsymptotics
