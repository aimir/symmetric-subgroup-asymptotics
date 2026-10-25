import SymmetricSubgroupAsymptotics.PrimitiveSocleProperIndexProductGap
import SymmetricSubgroupAsymptotics.ComponentOrderCubeWreathExtraGap
import SymmetricSubgroupAsymptotics.LogSquareOrderClassExtraGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound

/-! A proved component order cube at every proper simple index leaves
the proper-subnormal extra exponent for ALL actual socle factor counts.
One factor uses the actual quotient/intersection saving; several factors
use the full factorial reserve; the power form uses the same actual order
bound and subgroup. Both original degree forms remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_order_index_budget
    (D : NonaffineData G X) (hdegree : 2 ≤ Nat.card X)
    (hlarge : 1024 ≤ Nat.card D.Simple)
    (hbudget : ∀ K : Subgroup D.Simple, K ≠ ⊤ →
      (Nat.card D.Simple*Nat.card (Outer D.Simple))^3 ≤ 5^(K.index-1))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  by_cases hone : D.factorCount=1
  · exact D.proper_subnormal_class_cube_le_of_factor_one_order_index_budget
      hone hdegree hbudget H hH hne
  have htwo : 2 ≤ D.factorCount := by have hp := D.factorCount_pos; omega
  rcases D.indexForm with ⟨K, hK, hform⟩ | ⟨a, hka, hform⟩
  · have hm : 5 ≤ K.index := nonabelianSimple_proper_index_five_le
      (fun hc => D.noncommutative (isMulCommutative_iff.mpr hc)) K hK
    have hc : Nat.card (ConjClasses H) ≤
        (Nat.card D.Simple*Nat.card (Outer D.Simple))^D.factorCount *
          D.factorCount.factorial :=
      (Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective).trans
        (H.card_le_card_group.trans D.card_le_simple_outer_wreath)
    have hw := ComponentOrderCubeWreathExtraGap.wreath_order_cube_le
      (Nat.card D.Simple*Nat.card (Outer D.Simple)) K.index D.factorCount
      (by omega) htwo (hbudget K hK)
    simpa only [hform] using (Nat.pow_le_pow_left hc 3).trans hw
  · have ha : a ≠ 0 := by have hp := D.factorCount_pos; omega
    have hn : 1024 ≤ Nat.card X := by
      rw [hform]
      exact hlarge.trans (Nat.le_self_pow ha _)
    exact LogSquareOrderClassExtraGap.subgroup_class_cube_le _ hn
      (D.card_le_degree_pow_log_of_power_form a hka hform (by omega)) H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
