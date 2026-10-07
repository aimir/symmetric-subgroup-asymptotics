import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameOrderSixLocalCatalogue

/-!
# Point-stabilizer order-twelve local dispatcher

If an order-twelve point stabilizer has trivial center, its only eligible
order-three-or-noncommutative-order-six quotient is the displayed cyclic
order-three quotient.  Any subgroup of order four lies in a normal subgroup
of order four: its image in the order-three quotient has order dividing both
four and three.  A noncommutative order-six quotient would have a normal
order-two, hence central, kernel.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeEightLiteralLocalRowCatalogue

theorem surjectiveHom_kernel_card_four_of_twelve_to_three
    {H L : Type*} [Group H] [Finite H] [Group L] [Finite L]
    (f : H →* L) (hf : Function.Surjective f)
    (hH : Nat.card H = 12) (hL : Nat.card L = 3) :
    Nat.card f.ker = 4 := by
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv, hH, hL] at hcard
  omega

theorem surjectiveHom_kernel_card_two_of_twelve_to_six
    {H L : Type*} [Group H] [Finite H] [Group L] [Finite L]
    (f : H →* L) (hf : Function.Surjective f)
    (hH : Nat.card H = 12) (hL : Nat.card L = 6) :
    Nat.card f.ker = 2 := by
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv, hH, hL] at hcard
  omega

/-- In an order-twelve group, every subgroup of order four lies in every
normal subgroup of order four.  This is the quotient form of uniqueness of a
normal Sylow two-subgroup, and avoids any classification of order-twelve
groups. -/
theorem subgroup_card_four_le_normal_card_four_of_group_card_twelve
    {H : Type*} [Group H] [Finite H]
    (N K : Subgroup H) [N.Normal]
    (hH : Nat.card H = 12) (hN : Nat.card N = 4)
    (hK : Nat.card K = 4) :
    K ≤ N := by
  have hquot : Nat.card (H ⧸ N) = 3 := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hH, hN] at hcard
    omega
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  have hdvdK : Nat.card (K.map q) ∣ 4 := by
    simpa only [hK] using K.card_map_dvd q
  have hdvdQ : Nat.card (K.map q) ∣ 3 := by
    simpa only [hquot] using Subgroup.card_subgroup_dvd_card (K.map q)
  have himage : Nat.card (K.map q) = 1 := by
    apply Nat.dvd_one.mp
    simpa using Nat.dvd_gcd hdvdK hdvdQ
  have hmap : K.map q = ⊥ := (Subgroup.card_eq_one).mp himage
  intro x hx
  have hqx : q x ∈ K.map q := Subgroup.mem_map_of_mem q hx
  rw [hmap, Subgroup.mem_bot] at hqx
  have hxker : x ∈ q.ker := by
    simpa only [MonoidHom.mem_ker] using hqx
  simpa only [q, QuotientGroup.ker_mk'] using hxker

/-- A normal subgroup of order four in a group of order twelve is unique. -/
theorem normal_subgroup_card_four_unique_of_group_card_twelve
    {H : Type*} [Group H] [Finite H]
    (N K : Subgroup H) [N.Normal]
    (hH : Nat.card H = 12) (hN : Nat.card N = 4)
    (hK : Nat.card K = 4) :
    K = N := by
  exact Subgroup.eq_of_le_of_card_ge
    (subgroup_card_four_le_normal_card_four_of_group_card_twelve
      N K hH hN hK)
    (by rw [hN, hK])

/-- The unique eligible local row for the `A4`-shaped order-twelve
stabilizers occurring in the eight-frame catalogue. -/
noncomputable def singletonOfOrderTwelveCyclicThree
    (T : Subgroup (Equiv.Perm (Fin 8)))
    (R : DegreeEightLiteralLocalRow T)
    (hsource : Nat.card (MulAction.stabilizer T (0 : Fin 8)) = 12)
    (htarget : Nat.card R.ModelLocalGroup = 3)
    (hcenter :
      Subgroup.center (MulAction.stabilizer T (0 : Fin 8)) = ⊥) :
    DegreeEightLiteralLocalRowCatalogue T where
  Row := Unit
  row _ := R
  complete := by
    intro L _ _ f hf hcard
    rcases hcard with hL | ⟨hL, _hnoncomm⟩
    · have hfcard : Nat.card f.ker = 4 :=
        surjectiveHom_kernel_card_four_of_twelve_to_three
          f hf hsource hL
      have hRcard : Nat.card R.literalLocalMap.ker = 4 :=
        surjectiveHom_kernel_card_four_of_twelve_to_three
          R.literalLocalMap R.literalLocalMap_surjective hsource htarget
      have hkernels : f.ker = R.literalLocalMap.ker :=
        normal_subgroup_card_four_unique_of_group_card_twelve
          R.literalLocalMap.ker f.ker hsource hRcard hfcard
      refine ⟨(), surjectiveTargetEquivOfKernelEq f R.literalLocalMap
        hf R.literalLocalMap_surjective hkernels, ?_⟩
      exact surjectiveTargetEquivOfKernelEq_comp f R.literalLocalMap
        hf R.literalLocalMap_surjective hkernels
    · have hfcard : Nat.card f.ker = 2 :=
        surjectiveHom_kernel_card_two_of_twelve_to_six
          f hf hsource hL
      have hfcenter : f.ker ≤
          Subgroup.center (MulAction.stabilizer T (0 : Fin 8)) :=
        normal_card_two_le_center f.ker hfcard
      have hfbot : f.ker = ⊥ := by
        apply le_antisymm
        · simpa only [hcenter] using hfcenter
        · exact bot_le
      rw [hfbot] at hfcard
      norm_num at hfcard

end DegreeEightLiteralLocalRowCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
