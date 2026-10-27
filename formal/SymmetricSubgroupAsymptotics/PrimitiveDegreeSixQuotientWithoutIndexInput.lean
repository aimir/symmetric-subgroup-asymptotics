import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixSocleOrderWithoutIndexInput
import SymmetricSubgroupAsymptotics.SixPointGroupOrderConstraints
import SymmetricSubgroupAsymptotics.PrimitiveSimpleSocleExcludesSolubleNormal
import SymmetricSubgroupAsymptotics.PrimitiveSixExactProfileNormalGenerators

/-! Direct normal-subgroup consumers on the actual primitive six-point
top. The elementary minimum-order theorem supplies the socle exclusion; no A5/S5/A6/S6 model classification is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure PrimitiveDegreeSixRecognition

private theorem sixPoint_overSocleSixty_order_receipt :
    ∀ n : Fin 721,n.val∣720 → 60∣n.val →
      n.val=60 ∨ n.val=120 ∨ n.val=180 ∨ n.val=240 ∨ n.val=360 ∨ n.val=720 := by
  decide +kernel

namespace PrimitiveDegreeSixOrdinaryWithoutIndexInput

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 6)]
    [FaithfulSMul G (Fin 6)]

theorem nonaffine_socle_quotient_card_le_two
    (D : NonaffineData G (Fin 6)) :
    Nat.card (G⧸finiteGroupSocle G)≤2 := by
  have hd : Nat.card G∣720 := by
    have h := Subgroup.card_dvd_of_injective (MulAction.toPermHom G (Fin 6))
      (show Function.Injective (MulAction.toPermHom G (Fin 6)) from MulAction.toPerm_injective)
    simpa only [Nat.card_perm,Nat.card_fin] using h
  have hle : Nat.card G≤720 := Nat.le_of_dvd (by decide) hd
  have hm := (finiteGroupSocle G).card_mul_index
  have hcard := D.degreeSix_socle_card_without_index
  rw [←Subgroup.index_eq_card]
  rcases hcard with h60|h360
  · have h60div : 60∣Nat.card G := h60 ▸ (finiteGroupSocle G).card_subgroup_dvd_card
    rcases sixPoint_overSocleSixty_order_receipt ⟨Nat.card G,by omega⟩ hd h60div with
      h|h|h|h|h|h
    all_goals change Nat.card G = _ at h
    · rw [h60,h] at hm
      omega
    · rw [h60,h] at hm
      omega
    · let H := (MulAction.toPermHom G (Fin 6)).range
      have he := MonoidHom.ofInjective
        (show Function.Injective (MulAction.toPermHom G (Fin 6)) from MulAction.toPerm_injective)
      have hh : Nat.card H=180 := (Nat.card_congr he.toEquiv).symm.trans h
      exact ((sixPoint_subgroup_card_ne_180_240 H).1 hh).elim
    · let H := (MulAction.toPermHom G (Fin 6)).range
      have he := MonoidHom.ofInjective
        (show Function.Injective (MulAction.toPermHom G (Fin 6)) from MulAction.toPerm_injective)
      have hh : Nat.card H=240 := (Nat.card_congr he.toEquiv).symm.trans h
      exact ((sixPoint_subgroup_card_ne_180_240 H).2 hh).elim
    · have hb := faithfulSix_largeOrder_normal_card_ge (Or.inl h) (finiteGroupSocle G)
        (D.oneFactor_socle_nontrivial (PrimitiveSocleSevenPointSingleFactorWithoutIndexInput.factorCount_eq_one D (by decide) (by decide)))
      omega
    · have hb := faithfulSix_largeOrder_normal_card_ge (Or.inr h) (finiteGroupSocle G)
        (D.oneFactor_socle_nontrivial (PrimitiveSocleSevenPointSingleFactorWithoutIndexInput.factorCount_eq_one D (by decide) (by decide)))
      omega
  · rw [h360] at hm
    omega


end PrimitiveDegreeSixOrdinaryWithoutIndexInput
end SymmetricSubgroupAsymptotics
