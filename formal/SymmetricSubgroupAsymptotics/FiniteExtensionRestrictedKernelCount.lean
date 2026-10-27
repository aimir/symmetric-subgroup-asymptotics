import SymmetricSubgroupAsymptotics.FiniteExtensionFixedImageKernelLiftCount
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators

/-! Complete image/kernel/lift counting with an actual predicate on the
kernel intersection. All images and all whole lifts are retained. A small
actual quotient order pays both image count and generating tuple length. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteExtensionRestrictedKernelCount
open FiniteExtensionFixedImageKernelLiftCount

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
local instance subtypeFintype {G : Type} [Finite G] (P : G → Prop) : Fintype {x // P x} :=
  Fintype.ofFinite _
local instance subgroupFintype {G : Type} [Group G] [Finite G] : Fintype (Subgroup G) :=
  Fintype.ofFinite _

variable {E Q : Type} [Group E] [Group Q] (π : E →* Q) (P : Subgroup E → Prop)

abbrev KernelFamily := {K : Subgroup E // K≤π.ker ∧ P K}
abbrev Family := {L : Subgroup E // P (L⊓π.ker)}

def encode (L : Family π P) :
    Σ H : Subgroup Q,Σ K : KernelFamily π P,Fibre π H K.val :=
  ⟨L.val.map π,⟨L.val⊓π.ker,inf_le_right,L.property⟩,⟨L.val,rfl,rfl⟩⟩

theorem encode_injective : Function.Injective (encode π P) := by
  intro L M h
  apply Subtype.ext
  exact congrArg
    (fun z : Σ H : Subgroup Q,Σ K : KernelFamily π P,Fibre π H K.val => z.2.2.val) h

theorem card_family_le_of_tuples [Finite E] [Finite Q] (hπ : Function.Surjective π)
    (d : ℕ) (f : (H : Subgroup Q) → Fin d → H)
    (hf : ∀ H,Subgroup.closure (Set.range (f H))=⊤) :
    Nat.card (Family π P)≤
      Nat.card (Subgroup Q)*Nat.card (KernelFamily π P)*(Nat.card π.ker)^d := by
  calc
    Nat.card (Family π P)≤Nat.card (Σ H : Subgroup Q,Σ K : KernelFamily π P,Fibre π H K.val) :=
      Nat.card_le_card_of_injective (encode π P) (encode_injective π P)
    _=∑ H : Subgroup Q,∑ K : KernelFamily π P,Nat.card (Fibre π H K.val) := by
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro H _
      exact Nat.card_sigma
    _≤∑ _H : Subgroup Q,∑ _K : KernelFamily π P,(Nat.card π.ker)^d := by
      apply Finset.sum_le_sum
      intro H _
      exact Finset.sum_le_sum (fun K _ => card_fibre_le π hπ H K.val (f H) (hf H))
    _=Nat.card (Subgroup Q)*Nat.card (KernelFamily π P)*(Nat.card π.ker)^d := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card,Nat.mul_assoc]

theorem card_family_le_of_quotient_card [Finite E] [Finite Q] (hπ : Function.Surjective π)
    (d : ℕ) (hQ : Nat.card Q≤2^d) :
    Nat.card (Family π P)≤2^(d*d)*Nat.card (KernelFamily π P)*(Nat.card π.ker)^d := by
  have hex : ∀ H : Subgroup Q,∃ f : Fin d → H,Subgroup.closure (Set.range f)=⊤ := by
    intro H
    have hH : Nat.card H≤2^d :=
      (Nat.card_le_card_of_injective H.subtype H.subtype_injective).trans hQ
    exact paddedTupleClosure_surjective (R := H) d hH ⊤
  choose f hf using hex
  have hb := card_family_le_of_tuples π P hπ d f hf
  have hcount := subgroup_card_le_two_pow_sq (R := Q) d hQ
  exact hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcount))

end SymmetricSubgroupAsymptotics.FiniteExtensionRestrictedKernelCount
