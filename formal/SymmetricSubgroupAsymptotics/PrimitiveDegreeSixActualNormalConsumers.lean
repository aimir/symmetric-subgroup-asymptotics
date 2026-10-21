import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixSocleOrder
import SymmetricSubgroupAsymptotics.SixPointGroupOrderConstraints
import SymmetricSubgroupAsymptotics.PrimitiveSimpleSocleExcludesSolubleNormal
import SymmetricSubgroupAsymptotics.PrimitiveSixExactProfileNormalGenerators

/-! Direct normal-subgroup consumers on the actual primitive six-point
top. The retained simple-index inequality supplies the elementary socle
order exclusion; no A5/S5/A6/S6 model classification is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure PrimitiveDegreeSixRecognition

private theorem sixPoint_overSocleSixty_order_receipt :
    ∀ n : Fin 721,n.val∣720 → 60∣n.val →
      n.val=60 ∨ n.val=120 ∨ n.val=180 ∨ n.val=240 ∨ n.val=360 ∨ n.val=720 := by
  decide +kernel

namespace PrimitiveDegreeSixActualNormalConsumers

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 6)]
    [FaithfulSMul G (Fin 6)]

theorem nonaffine_socle_quotient_card_le_two
    (D : NonaffineData G (Fin 6)) (hindex : PublishedSimpleIndexBounds) :
    Nat.card (G⧸finiteGroupSocle G)≤2 := by
  have hd : Nat.card G∣720 := by
    have h := Subgroup.card_dvd_of_injective (MulAction.toPermHom G (Fin 6))
      (show Function.Injective (MulAction.toPermHom G (Fin 6)) from MulAction.toPerm_injective)
    simpa only [Nat.card_perm,Nat.card_fin] using h
  have hle : Nat.card G≤720 := Nat.le_of_dvd (by decide) hd
  have hm := (finiteGroupSocle G).card_mul_index
  have hcard := D.degreeSix_socle_card hindex
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
        (D.oneFactor_socle_nontrivial (D.degreeSix_factorCount_one hindex))
      omega
    · have hb := faithfulSix_largeOrder_normal_card_ge (Or.inr h) (finiteGroupSocle G)
        (D.oneFactor_socle_nontrivial (D.degreeSix_factorCount_one hindex))
      omega
  · rw [h360] at hm
    omega

/-- The impossible affine branch is discharged before any source is
chosen, retaining the original top and its literal full socle. -/
def nonaffineData [MulAction.IsPreprimitive G (Fin 6)] : NonaffineData G (Fin 6) :=
  Classical.choice <| by
    cases Classical.choice (publishedONanScottStructure G (Fin 6)) with
    | inl D => exact ⟨D⟩
    | inr P =>
        have hp : P.p=2 := P.prime_eq_two_of_even_degree (0 : Fin 6) (by decide)
        obtain ⟨d,hd⟩ := P.degree_eq_prime_power (0 : Fin 6)
        rw [hp] at hd
        exact (PrimitiveSixExactProfileNormalGenerators.six_not_two_power d hd).elim

variable (hindex : PublishedSimpleIndexBounds)
    [MulAction.IsPreprimitive G (Fin 6)]

include hindex in
theorem socle_quotient_card_le_two : Nat.card (G⧸finiteGroupSocle G)≤2 :=
  nonaffine_socle_quotient_card_le_two (nonaffineData (G := G)) hindex

include hindex in
theorem normal_total (A B : Subgroup G) (hA : A.Normal) (hB : B.Normal) : A≤B ∨ B≤A := by
  let D := nonaffineData (G := G)
  exact PrimitiveSixExactProfileNormalGenerators.normal_total_of_unique_minimal_small_quotient
    (finiteGroupSocle G) (D.oneFactor_socle_le (D.degreeSix_factorCount_one hindex))
    (socle_quotient_card_le_two hindex) A B hA hB

include hindex in
theorem normal_generating_singletons (N : Subgroup G) (hN : N.Normal) :
    ∃ x : Fin 1→G,Subgroup.normalClosure (Set.range x)=N :=
  normal_generating_singletons_of_finite_normal_total (normal_total hindex) N hN

include hindex in
theorem normalGen_le_one (N : Subgroup G) [N.Normal] : MarkedC4.normalGen N≤1 := by
  obtain ⟨x,hx⟩ := normal_generating_singletons hindex N inferInstance
  exact normalGen_le_of_fin_tuple x hx

include hindex in
theorem noAbelianNormal (N : Subgroup G) (hN : N.Normal) (hc : IsMulCommutative N) : N=⊥ := by
  by_contra hne
  letI := hN
  letI : IsSolvable N := isSolvable_of_comm hc.is_comm.comm
  let D := nonaffineData (G := G)
  exact D.oneFactor_no_nontrivial_soluble_normal
    (D.degreeSix_factorCount_one hindex) N hne

include hindex in
theorem normal_quotient_card_le_two
    (N : Subgroup G) (hN : N.Normal) (hne : N≠⊥) : Nat.card (G⧸N)≤2 := by
  letI := hN
  let D := nonaffineData (G := G)
  have hle := D.oneFactor_socle_le (D.degreeSix_factorCount_one hindex) N hN hne
  calc
    Nat.card (G⧸N)=N.index := N.index_eq_card.symm
    _ ≤ (finiteGroupSocle G).index := Subgroup.index_antitone hle
    _ = Nat.card (G⧸finiteGroupSocle G) := (finiteGroupSocle G).index_eq_card
    _ ≤ 2 := socle_quotient_card_le_two hindex

end PrimitiveDegreeSixActualNormalConsumers
end SymmetricSubgroupAsymptotics
