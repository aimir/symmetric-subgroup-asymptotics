import SymmetricSubgroupAsymptotics.NormalImageIntersectionCard
import SymmetricSubgroupAsymptotics.NormalFPacketOfActualCards

/-! A proper normal subgroup keeps its original mixed commutator and the
same original denominator. An intersection shared with N is paid only once. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics
open MarkedC4.RDTNormalFInterface
variable {G : Type} [Group G] [Finite G]

theorem targetCommutator_quotient_le_image
    (N F C : Subgroup G) [N.Normal]
    (hFC : ⁅F, (⊤ : Subgroup G)⁆ ≤ C) :
    targetCommutator (F.map (QuotientGroup.mk' N)) ≤ C.map (QuotientGroup.mk' N) := by
  have htop : (⊤ : Subgroup G).map (QuotientGroup.mk' N) = ⊤ :=
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)
  change ⁅F.map (QuotientGroup.mk' N), ⊤⁆ ≤ _
  rw [← htop, ← Subgroup.map_commutator]
  exact Subgroup.map_mono hFC

theorem targetCommutator_quotient_card_mul_le
    (N F C B : Subgroup G) [N.Normal]
    (hFC : ⁅F, (⊤ : Subgroup G)⁆ ≤ C)
    (hBC : B ≤ C) (hBN : B ≤ N) :
    Nat.card (targetCommutator (F.map (QuotientGroup.mk' N))) * Nat.card B ≤ Nat.card C := by
  have hm := targetCommutator_quotient_le_image N F C hFC
  have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hm)
    (Subgroup.inclusion_injective hm)
  exact (Nat.mul_le_mul_right _ hc).trans
    (normal_quotient_image_card_mul_le_of_shared_subgroup N C B hBC hBN)

theorem targetCommutator_quotient_card_le
    (N F C B : Subgroup G) [N.Normal]
    (hFC : ⁅F, (⊤ : Subgroup G)⁆ ≤ C)
    (hBC : B ≤ C) (hBN : B ≤ N) (d : ℕ)
    (hC : Nat.card C ≤ 2 ^ d * Nat.card B) :
    Nat.card (targetCommutator (F.map (QuotientGroup.mk' N))) ≤ 2 ^ d := by
  have h := (targetCommutator_quotient_card_mul_le N F C B hFC hBC hBN).trans hC
  exact Nat.le_of_mul_le_mul_right h (Nat.card_pos (α := B))

end SymmetricSubgroupAsymptotics
