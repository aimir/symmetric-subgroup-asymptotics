import SymmetricSubgroupAsymptotics.FiniteAbelianExtensionWholeLayerCount

/-! Complete quotient-image aggregation in an actual finite extension.
Every literal subgroup is retained, with its actual image and its full
subgroup in the preimage extension. Kernel-only data do not encode it.
No splitting, transitivity, generator bound, or counting input is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteExtensionQuotientImageCount
open FiniteAbelianExtensionWholeLayerCount

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective

local instance subgroupFintype {G : Type} [Group G] [Finite G] : Fintype (Subgroup G) :=
  Fintype.ofFinite _

variable {E Q : Type} [Group E] [Group Q]

abbrev ImageFibre (π : E →* Q) (H : Subgroup Q) :=
  {L : Subgroup E // L.map π = H}

private theorem le_preimage (π : E →* Q) (H : Subgroup Q) (L : ImageFibre π H) :
    L.val ≤ H.comap π := by
  intro x hx
  change π x ∈ H
  rw [←L.property]
  exact ⟨x,hx,rfl⟩

/-- Restrict the whole literal subgroup to the actual preimage of its image. -/
def toFullImage (π : E →* Q) (H : Subgroup Q) (L : ImageFibre π H) :
    FullImage (π.subgroupComap H) := by
  refine ⟨L.val.subgroupOf (H.comap π),?_⟩
  apply top_unique
  intro q _
  have hq : (q : Q) ∈ L.val.map π := by rw [L.property]; exact q.property
  obtain ⟨x,hx,he⟩ := hq
  have hpre : x ∈ H.comap π := le_preimage π H L hx
  exact ⟨⟨x,hpre⟩,hx,Subtype.ext he⟩

theorem toFullImage_injective (π : E →* Q) (H : Subgroup Q) :
    Function.Injective (toFullImage π H) := by
  intro L M he
  have hh := congrArg (fun K : Subgroup (H.comap π) => K.map (H.comap π).subtype)
    (congrArg Subtype.val he)
  change (L.val.subgroupOf (H.comap π)).map (H.comap π).subtype =
    (M.val.subgroupOf (H.comap π)).map (H.comap π).subtype at hh
  rw [Subgroup.map_subgroupOf_eq_of_le (le_preimage π H L),
    Subgroup.map_subgroupOf_eq_of_le (le_preimage π H M)] at hh
  exact Subtype.ext hh

/-- Every subgroup is assigned its ACTUAL quotient image, retaining its full lift. -/
def encode (π : E →* Q) (L : Subgroup E) :
    Σ H : Subgroup Q, FullImage (π.subgroupComap H) :=
  ⟨L.map π,toFullImage π (L.map π) ⟨L,rfl⟩⟩

private def forget (π : E →* Q)
    (a : Σ H : Subgroup Q, FullImage (π.subgroupComap H)) : Subgroup E :=
  a.2.val.map (a.1.comap π).subtype

theorem encode_injective (π : E →* Q) : Function.Injective (encode π) := by
  have hi : Function.LeftInverse (forget π) (encode π) := by
    intro L
    exact Subgroup.map_subgroupOf_eq_of_le (le_preimage π (L.map π) ⟨L,rfl⟩)
  exact hi.injective

/-- Counts all image choices AND all extension fibres; no kernel-only shortcut. -/
theorem card_subgroup_le_sum_fullImage [Finite E] [Finite Q] (π : E →* Q) :
    Nat.card (Subgroup E) ≤
      ∑ H : Subgroup Q, Nat.card (FullImage (π.subgroupComap H)) := by
  have hh := Nat.card_le_card_of_injective (encode π) (encode_injective π)
  simpa only [Nat.card_sigma] using hh

/-- Any proved bounds on the literal full-image fibres may now be summed. -/
theorem card_subgroup_le_of_image_bounds [Finite E] [Finite Q] (π : E →* Q)
    (B : Subgroup Q → ℕ)
    (hB : ∀ H : Subgroup Q, Nat.card (FullImage (π.subgroupComap H)) ≤ B H) :
    Nat.card (Subgroup E) ≤ ∑ H : Subgroup Q, B H :=
  (card_subgroup_le_sum_fullImage π).trans (Finset.sum_le_sum (fun H _ => hB H))

end SymmetricSubgroupAsymptotics.FiniteExtensionQuotientImageCount
