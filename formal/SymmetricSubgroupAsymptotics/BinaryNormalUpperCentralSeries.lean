import SymmetricSubgroupAsymptotics.PGroupNormalIndexP
import SymmetricSubgroupAsymptotics.QuotientSubgroupImageCard
import Mathlib.GroupTheory.Nilpotent

/-! A small original normal subgroup lies in the corresponding actual
upper central term. Its quotient-centre preimage lies in the NEXT term,
and its exact original order pays the quotient-centre cardinality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics
local instance normalUpperCentralSeriesPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {G : Type} [Group G] [Finite G]

theorem binary_normal_le_upperCentralSeries_of_card_le
    (hG : IsPGroup 2 G) (k : ℕ) (L : Subgroup G) [L.Normal]
    (hcard : Nat.card L≤2^k) : L≤Subgroup.upperCentralSeries G k := by
  induction k generalizing L with
  | zero =>
    rw [Subgroup.upperCentralSeries_zero]
    exact le_of_eq (L.eq_bot_of_card_le (by simpa only [pow_zero] using hcard))
  | succ k ih =>
    by_cases hbot : L=⊥
    · exact hbot ▸ bot_le
    obtain ⟨J,hJ,_,hJL,hindex⟩ := pGroup_normal_interval_top_step hG
      (⊥ : Subgroup G) L (bot_lt_iff_ne_bot.mpr hbot)
    letI : J.Normal := hJ
    have hJcard : Nat.card J≤2^k := by
      have hc := (J.subgroupOf L).card_mul_index
      have he : Nat.card (J.subgroupOf L)=Nat.card J :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJL.le).toEquiv
      change Nat.card (J.subgroupOf L)*J.relIndex L=Nat.card L at hc
      rw [he,hindex] at hc
      rw [pow_succ] at hcard
      nlinarith
    have hJZ := ih J hJcard
    intro x hx
    apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
    intro y
    apply hJZ
    have hz := pGroup_normal_index_p_central hG J L hJL.le hindex x hx
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' J) ⁅x,y⁆=1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp hz (QuotientGroup.mk' J y)).symm

/-- This preimage argument is independent of the p-group hypothesis. It
retains the SAME original denominator and the literal upper central term. -/
theorem normal_quotient_center_card_mul_le_upperCentralSeries
    (L : Subgroup G) [L.Normal] (k : ℕ)
    (hL : L≤Subgroup.upperCentralSeries G k) :
    Nat.card L*Nat.card (Subgroup.center (G ⧸ L))≤
      Nat.card (Subgroup.upperCentralSeries G (k+1)) := by
  let q := QuotientGroup.mk' L
  let P := (Subgroup.center (G ⧸ L)).comap q
  have hLP : L≤P := by
    intro x hx
    change q x∈Subgroup.center (G ⧸ L)
    have he : q x=1 := (QuotientGroup.eq_one_iff _).mpr hx
    rw [he]
    exact Subgroup.one_mem _
  have hPZ : P≤Subgroup.upperCentralSeries G (k+1) := by
    intro x hx
    apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
    intro y
    apply hL
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅x,y⁆=1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp hx (q y)).symm
  have hmap : P.map q=Subgroup.center (G ⧸ L) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective L) _
  have hc := quotient_subgroup_image_card_mul_intersection L P
  rw [inf_eq_left.mpr hLP,hmap] at hc
  exact hc.le.trans (Subgroup.card_le_of_le hPZ)

/-- The complete generic low-order-normal capacity. No central-layer
census, source model, or independent normal subgroup is introduced. -/
theorem binary_normal_quotient_center_card_mul_le_upperCentralSeries_of_card_le
    (hG : IsPGroup 2 G) (k : ℕ) (L : Subgroup G) [L.Normal]
    (hcard : Nat.card L≤2^k) :
    Nat.card L*Nat.card (Subgroup.center (G ⧸ L))≤
      Nat.card (Subgroup.upperCentralSeries G (k+1)) :=
  normal_quotient_center_card_mul_le_upperCentralSeries L k
    (binary_normal_le_upperCentralSeries_of_card_le hG k L hcard)
end SymmetricSubgroupAsymptotics
