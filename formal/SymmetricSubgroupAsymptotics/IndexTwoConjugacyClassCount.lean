import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

/-! Commuting-pair counting across one actual index-two subgroup.
An outside element has its centralizer in the kernel detected by a fixed
projection. All four source rectangles remain in the count. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.IndexTwoConjugacyClassCount

variable {G H : Type} [Group G] [Group H]
    (K : Subgroup G) (hi : K.index = 2) (f : K →* H)
    (hinj : ∀ x : G, x ∉ K → ∀ y z : K,
      Commute x (y : G) → Commute x (z : G) → f y = f z → y = z)

private abbrev Outside := {x : G // x ∉ K}
private abbrev InsidePairs := {p : K × K // Commute p.1 p.2}

include hi in
private theorem difference_mem (x y : G) (hx : x ∉ K) (hy : y ∉ K) :
    x⁻¹ * y ∈ K := by
  rw [K.mul_mem_iff_of_index_two hi, K.inv_mem_iff]
  exact iff_of_false hx hy

include hi in
private def encode (p : {p : G × G // Commute p.1 p.2}) :
    InsidePairs K ⊕ (Fin 3 × Outside K × H) :=
  if hx : p.1.1 ∈ K then
    if hy : p.1.2 ∈ K then
      .inl ⟨(⟨p.1.1,hx⟩,⟨p.1.2,hy⟩), by
        exact Subtype.ext p.2.eq⟩
    else .inr (1, ⟨p.1.2,hy⟩, f ⟨p.1.1,hx⟩)
  else
    if hy : p.1.2 ∈ K then
      .inr (0, ⟨p.1.1,hx⟩, f ⟨p.1.2,hy⟩)
    else .inr (2, ⟨p.1.1,hx⟩,
      f ⟨p.1.1⁻¹*p.1.2,difference_mem K hi _ _ hx hy⟩)

include hi hinj in
private theorem encode_injective : Function.Injective (encode K hi f) := by
  rintro ⟨⟨x,y⟩,hc⟩ ⟨⟨u,v⟩,hd⟩ he
  by_cases hx : x ∈ K <;> by_cases hy : y ∈ K <;>
    by_cases hu : u ∈ K <;> by_cases hv : v ∈ K <;>
    simp [encode, hx, hy, hu, hv] at he
  · exact Subtype.ext (Prod.ext he.1 he.2)
  · rcases he with ⟨rfl,hf⟩
    have hxu := hinj y hy ⟨x,hx⟩ ⟨u,hu⟩ hc.symm hd.symm hf
    exact Subtype.ext (Prod.ext (congrArg Subtype.val hxu) rfl)
  · rcases he with ⟨rfl,hf⟩
    have hyv := hinj x hx ⟨y,hy⟩ ⟨v,hv⟩ hc hd hf
    exact Subtype.ext (Prod.ext rfl (congrArg Subtype.val hyv))
  · rcases he with ⟨rfl,hf⟩
    have hyv := hinj x hx
      ⟨x⁻¹*y,difference_mem K hi _ _ hx hy⟩
      ⟨x⁻¹*v,difference_mem K hi _ _ hx hv⟩
      ((Commute.refl x).inv_right.mul_right hc)
      ((Commute.refl x).inv_right.mul_right hd) hf
    exact Subtype.ext (Prod.ext rfl (mul_left_cancel (congrArg Subtype.val hyv)))

variable [Finite G] [Finite H]

include hi f hinj in
/-- The actual group class count, after cancelling the original kernel
order. The hypothesis is injectivity of a projection on each outside
centralizer; it makes no class-number or group-classification assumption. -/
theorem double_class_card_le :
    2 * Nat.card (ConjClasses G) ≤ Nat.card (ConjClasses K) + 3 * Nat.card H := by
  have hcardG : Nat.card G = 2 * Nat.card K := by
    have h := K.card_mul_index
    rw [hi] at h
    omega
  have houtside : Nat.card (Outside K) = Nat.card K := by
    have h := Nat.card_congr (Equiv.Set.sumCompl (K : Set G))
    rw [Nat.card_sum] at h
    change Nat.card K + Nat.card (Outside K) = Nat.card G at h
    omega
  have hraw := Nat.card_le_card_of_injective (encode K hi f)
    (encode_injective K hi f hinj)
  simp only [Nat.card_sum, Nat.card_prod, Nat.card_fin] at hraw
  change Nat.card {p : G × G // Commute p.1 p.2} ≤
    Nat.card {p : K × K // Commute p.1 p.2} +
      3 * (Nat.card (Outside K) * Nat.card H) at hraw
  rw [houtside, card_comm_eq_card_conjClasses_mul_card,
    card_comm_eq_card_conjClasses_mul_card] at hraw
  rw [hcardG] at hraw
  have hpos := Nat.card_pos (α := K)
  nlinarith

end SymmetricSubgroupAsymptotics.IndexTwoConjugacyClassCount
