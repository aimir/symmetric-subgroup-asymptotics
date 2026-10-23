import SymmetricSubgroupAsymptotics.CFSGDisjointSubgroupProductCard
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Product cardinalities inside an actual containing subgroup, and
the preservation of conjugate-subgroup cardinalities under a homomorphism. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSubgroupProductInside
variable {G H : Type*} [Group G] [Group H]

theorem card_mul_le (B P T : Subgroup G) [Finite B]
    (hP : P ≤ B) (hT : T ≤ B) (hPT : P ⊓ T = ⊥) :
    Nat.card P * Nat.card T ≤ Nat.card B := by
  have hbot : P.subgroupOf B ⊓ T.subgroupOf B = ⊥ := by
    apply bot_unique
    rintro x ⟨hxP, hxT⟩
    have hh : x.val ∈ P ⊓ T := ⟨hxP, hxT⟩
    have he : x.val = 1 := by simpa only [hPT, Subgroup.mem_bot] using hh
    exact Subtype.ext he
  have hh := CFSGDisjointSubgroupProductCard.card_mul_le (P.subgroupOf B) (T.subgroupOf B) hbot
  have hp : Nat.card (P.subgroupOf B) = Nat.card P :=
    Nat.card_congr (P.subgroupOfEquivOfLe hP).toEquiv
  have ht : Nat.card (T.subgroupOf B) = Nat.card T :=
    Nat.card_congr (T.subgroupOfEquivOfLe hT).toEquiv
  rwa [hp, ht] at hh

theorem map_conjugate (f : G →* H) (P : Subgroup G) (w : G) :
    (P.map (MulAut.conj w).toMonoidHom).map f =
      (P.map f).map (MulAut.conj (f w)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem map_conjugate_card (f : G →* H) (P : Subgroup G) (w : G) :
    Nat.card ((P.map (MulAut.conj w).toMonoidHom).map f) = Nat.card (P.map f) := by
  rw [map_conjugate]
  exact Subgroup.card_map_of_injective (MulAut.conj (f w)).injective

end SymmetricSubgroupAsymptotics.CFSGSubgroupProductInside
