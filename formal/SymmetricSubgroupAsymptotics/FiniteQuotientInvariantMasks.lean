import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantCertificates
import SymmetricSubgroupAsymptotics.FiniteQuotientDerivedIntersection

/-! Exact quotient invariants from finite tests on original elements.
Center masks test the original generating tuple. The derived cardinality
uses the literal intersection N ∩ G', including normals outside G'. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G ι α : Type*} [Group G]

theorem quotientCenterPreimage_card_of_mask (N : Subgroup G) [N.Normal]
    (generators : ι → G) (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (e : α ≃ G) (mask : α → Prop)
    (hmask : ∀ a, mask a ↔ ∀ j, ⁅e a, generators j⁆ ∈ N) :
    Nat.card (quotientCenterPreimage N) = Nat.card {a // mask a} := by
  let f : {a // mask a} ≃ quotientCenterPreimage N :=
    e.subtypeEquiv (fun a => (hmask a).trans
      (mem_quotientCenterPreimage_iff N generators hgen (e a)).symm)
  exact (Nat.card_congr f).symm

theorem quotientCenter_card_of_mask [Finite G] (N : Subgroup G) [N.Normal]
    (generators : ι → G) (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (e : α ≃ G) (mask : α → Prop)
    (hmask : ∀ a, mask a ↔ ∀ j, ⁅e a, generators j⁆ ∈ N)
    (c : ℕ) (hcard : Nat.card {a // mask a} = c * Nat.card N) :
    Nat.card (Subgroup.center (G ⧸ N)) = c := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := N))
  exact (quotientCenter_card_mul N).trans
    ((quotientCenterPreimage_card_of_mask N generators hgen e mask hmask).trans hcard)

theorem quotientCommutator_card_of_inf_card [Finite G]
    (N : Subgroup G) [N.Normal] (g : ℕ)
    (hcard : Nat.card (commutator G) = g * Nat.card ↥(N ⊓ commutator G)) :
    Nat.card (commutator (G ⧸ N)) = g := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(N ⊓ commutator G)))
  exact (quotientCommutator_card_mul_inf N).trans hcard

end SymmetricSubgroupAsymptotics
