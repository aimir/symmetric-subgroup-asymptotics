import SymmetricSubgroupAsymptotics.NormalIntegralCoinvariantExtension

/-! Exact integral filtration across an actual quotient. The denominator
is the actual intersection [N,G]∩ker f, so extra mixed commutators are
retained rather than replaced by the smaller radical of N∩ker f. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G H : Type} [Group G] [Finite G] [Group H] [Finite H]

private theorem integralIntersection_relIndex_mul_card
    (A B : Subgroup G) (hBA : B≤A) : B.relIndex A*Nat.card B=Nat.card A := by
  have hc := (B.subgroupOf A).card_mul_index
  have he : Nat.card (B.subgroupOf A)=Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
  rw [he] at hc
  exact (Nat.mul_comm _ _).trans hc

theorem normalIntegralCoinvariantOrder_mul_actual_commutator_intersection
    (f : G →* H) (hf : Function.Surjective f) (N : Subgroup G) [N.Normal] :
    normalIntegralCoinvariantOrder N*
      Nat.card (⁅N,(⊤ : Subgroup G)⁆ ⊓ f.ker : Subgroup G)=
      normalIntegralCoinvariantOrder (N.map f)*Nat.card (N ⊓ f.ker : Subgroup G) := by
  let C := ⁅N,(⊤ : Subgroup G)⁆
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hmap : C.map f=⁅N.map f,(⊤ : Subgroup H)⁆ := by
    dsimp only [C]
    rw [Subgroup.map_commutator,Subgroup.map_top_of_surjective f hf]
  have hN := subgroup_card_eq_map_mul_kernel_intersection f N
  have hC := subgroup_card_eq_map_mul_kernel_intersection f C
  have hs : normalIntegralCoinvariantOrder N*Nat.card C=Nat.card N :=
    integralIntersection_relIndex_mul_card N C (Subgroup.commutator_le_left N ⊤)
  have ht : normalIntegralCoinvariantOrder (N.map f)*Nat.card (C.map f)=Nat.card (N.map f) := by
    rw [hmap]
    exact integralIntersection_relIndex_mul_card (N.map f) _
      (Subgroup.commutator_le_left (N.map f) ⊤)
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := C.map f))
  calc
    Nat.card (C.map f)*(normalIntegralCoinvariantOrder N*Nat.card (C ⊓ f.ker : Subgroup G)) =
        normalIntegralCoinvariantOrder N*Nat.card C := by rw [hC];ring
    _ = Nat.card N := hs
    _ = Nat.card (N.map f)*Nat.card (N ⊓ f.ker : Subgroup G) := hN
    _ = Nat.card (C.map f)*(normalIntegralCoinvariantOrder (N.map f)*
        Nat.card (N ⊓ f.ker : Subgroup G)) := by rw [←ht];ring

/-- A retained extra bit in the actual mixed intersection is available
to the integral budget; no normal-rank monotonicity is used. -/
theorem normalIntegralCoinvariantOrder_le_of_actual_intersection_budget
    (f : G →* H) (hf : Function.Surjective f) (N : Subgroup G) [N.Normal]
    (b : ℕ) (hbudget : Nat.card (N ⊓ f.ker : Subgroup G)≤
      b*Nat.card (⁅N,(⊤ : Subgroup G)⁆ ⊓ f.ker : Subgroup G)) :
    normalIntegralCoinvariantOrder N≤b*normalIntegralCoinvariantOrder (N.map f) := by
  have he := normalIntegralCoinvariantOrder_mul_actual_commutator_intersection f hf N
  have hm := Nat.mul_le_mul_left (normalIntegralCoinvariantOrder (N.map f)) hbudget
  rw [←he] at hm
  have hb : normalIntegralCoinvariantOrder N*
      Nat.card (⁅N,(⊤ : Subgroup G)⁆ ⊓ f.ker : Subgroup G)≤
      (b*normalIntegralCoinvariantOrder (N.map f))*
        Nat.card (⁅N,(⊤ : Subgroup G)⁆ ⊓ f.ker : Subgroup G) := by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hm
  exact Nat.le_of_mul_le_mul_right hb Nat.card_pos

end SymmetricSubgroupAsymptotics
