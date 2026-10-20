import SymmetricSubgroupAsymptotics.DirectProductNormalGenerators
import SymmetricSubgroupAsymptotics.FiniteThreeNormalChainSocleGenerators
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.ZMod.Basic

/-!
# A literal diagonal action with a binary block swap

An explicit point chart identifies two copies of an action with a product
action. Both closure inclusions are supplied by actual generator bindings;
no group-order comparison or splitting assertion about normal subgroups is
used. A finite normal chain in the local factor then gives two ambient normal
generators in the original permutation group.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DiagonalBinaryPermutationProduct

abbrev Binary := Multiplicative (ZMod 2)

def bit : Binary := Multiplicative.ofAdd 1

theorem binary_cases (c : Binary) : c = 1 ∨ c = bit := by
  decide +kernel +revert

variable {X P : Type}

def productAction : Equiv.Perm X × Binary →* Equiv.Perm (X × Binary) where
  toFun g :=
    { toFun := fun p ↦ (g.1 p.1, g.2 * p.2)
      invFun := fun p ↦ (g.1.symm p.1, g.2⁻¹ * p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }
  map_one' := by ext p <;> simp
  map_mul' g h := by ext p <;> simp [mul_assoc]

def literalAction (e : P ≃ X × Binary) :
    Equiv.Perm X × Binary →* Equiv.Perm P :=
  e.symm.permCongrHom.toMonoidHom.comp productAction

def diagonal (e : P ≃ X × Binary) : Equiv.Perm X →* Equiv.Perm P :=
  (literalAction e).comp (MonoidHom.inl (Equiv.Perm X) Binary)

def toggle (e : P ≃ X × Binary) : Equiv.Perm P :=
  literalAction e (1, bit)

def action (L : Subgroup (Equiv.Perm X)) (e : P ≃ X × Binary) :
    L × Binary →* Equiv.Perm P :=
  (literalAction e).comp (L.subtype.prodMap (MonoidHom.id Binary))

theorem productAction_injective [Nonempty X] :
    Function.Injective (productAction (X := X)) := by
  intro g h he
  apply Prod.ext
  · apply Equiv.ext
    intro x
    exact congrArg (fun p : Equiv.Perm (X × Binary) ↦ (p (x, 1)).1) he
  · obtain ⟨x⟩ := ‹Nonempty X›
    have hc := congrArg (fun p : Equiv.Perm (X × Binary) ↦ (p (x, 1)).2) he
    change g.2 * 1 = h.2 * 1 at hc
    simpa only [mul_one] using hc

theorem action_injective [Nonempty X]
    (L : Subgroup (Equiv.Perm X)) (e : P ≃ X × Binary) :
    Function.Injective (action L e) := by
  intro g h he
  have hlit : productAction ((g.1 : Equiv.Perm X), g.2) =
      productAction ((h.1 : Equiv.Perm X), h.2) :=
    e.symm.permCongrHom.injective he
  have hp : ((g.1 : Equiv.Perm X), g.2) = ((h.1 : Equiv.Perm X), h.2) :=
    productAction_injective hlit
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun z : Equiv.Perm X × Binary ↦ z.1) hp)
  · exact congrArg (fun z : Equiv.Perm X × Binary ↦ z.2) hp

@[simp] theorem action_one (L : Subgroup (Equiv.Perm X))
    (e : P ≃ X × Binary) (g : L) :
    action L e (g, 1) = diagonal e (g : Equiv.Perm X) := rfl

theorem action_bit (L : Subgroup (Equiv.Perm X))
    (e : P ≃ X × Binary) (g : L) :
    action L e (g, bit) = diagonal e (g : Equiv.Perm X) * toggle e := by
  change literalAction e ((g : Equiv.Perm X), bit) =
    literalAction e ((g : Equiv.Perm X), 1) * literalAction e (1, bit)
  rw [← map_mul]
  simp

/-- Exact generator bindings and reverse words identify the original closure. -/
theorem action_range_eq {ι κ : Type}
    (localGenerators : ι → Equiv.Perm X) (e : P ≃ X × Binary)
    (generators : κ → Equiv.Perm P)
    (modelGenerators : κ → Subgroup.closure (Set.range localGenerators) × Binary)
    (binding : ∀ i,
      action (Subgroup.closure (Set.range localGenerators)) e (modelGenerators i) = generators i)
    (diagonal_mem : ∀ i, diagonal e (localGenerators i) ∈
      Subgroup.closure (Set.range generators))
    (toggle_mem : toggle e ∈ Subgroup.closure (Set.range generators)) :
    (action (Subgroup.closure (Set.range localGenerators)) e).range =
      Subgroup.closure (Set.range generators) := by
  let T := Subgroup.closure (Set.range generators)
  have hd : Subgroup.closure (Set.range localGenerators) ≤
      T.comap (diagonal e) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact diagonal_mem i
  apply le_antisymm
  · rintro _ ⟨⟨g, c⟩, rfl⟩
    have hg : diagonal e (g : Equiv.Perm X) ∈ T := hd g.property
    rcases binary_cases c with rfl | rfl
    · simpa only [action_one] using hg
    · rw [action_bit]
      exact T.mul_mem hg toggle_mem
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, binding i⟩

theorem binary_normal_total (K L : Subgroup Binary) (_hK : K.Normal) (_hL : L.Normal) :
    K ≤ L ∨ L ≤ K := by
  letI : Fact (Nat.card Binary).Prime := ⟨by
    rw [Nat.card_eq_fintype_card]
    decide +kernel⟩
  rcases K.eq_bot_or_eq_top_of_prime_card with rfl | rfl <;> simp

theorem normal_total_of_three_chain {G : Type} [Group G]
    (D : FiniteThreeNormalChainData G)
    (K L : Subgroup G) (hK : K.Normal) (hL : L.Normal) : K ≤ L ∨ L ≤ K := by
  rcases D.normal_eq_bot_or_middle_or_top K hK with rfl | rfl | rfl <;>
    rcases D.normal_eq_bot_or_middle_or_top L hL with rfl | rfl | rfl <;> simp

/-- Transport the product bound to the original top; normal subgroups of a
product are handled by intersection and projection, without a splitting premise. -/
theorem normal_generating_pairs_of_equiv {G H : Type}
    [Group G] [Group H] [Finite G]
    (D : FiniteThreeNormalChainData G) (e : G × Binary ≃* H) :
    ∀ N : Subgroup H, N.Normal →
      ∃ x : Fin 2 → H, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective e.toMonoidHom e.surjective
    (normal_generating_pairs_prod_of_normal_total
      (normal_total_of_three_chain D) binary_normal_total)

end DiagonalBinaryPermutationProduct
end SymmetricSubgroupAsymptotics

end
