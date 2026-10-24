import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddlePairingIndex
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOrderLower
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.FFourHeisenbergOrderCubeNumerics

/-! The actual fixed middle pairing pays the original triality primitive
component at every field order at least three. The same raw socle,
all factor counts and both primitive degree forms are retained. The
binary field remains explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_triality_field_ge_three
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.TrialityD4 q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.TrialityD4 q) :=
    fun h=>D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hb : 3 ≤ 2*q.order^4 := by
    have hp := Nat.pow_le_pow_left hq 4
    omega
  refine D.subgroup_class_cube_le_of_component_order_cube (2*q.order^4) hb ?_ ?_ ?_ H
  · intro K hK
    have hproper : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGTrialityGeckMiddlePairingIndex.typeTriality_middle_le_proper_index
      q (K.map e.toMonoidHom) hproper
    have hindex : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    exact ((Nat.mul_le_mul_right (q.order^4) q.prime_isPrime.two_le).trans hi).trans_eq hindex
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    have hc : Nat.card (CFSG.Models.TrialityD4 q)*
        Nat.card (Outer (CFSG.Models.TrialityD4 q)) ≤ q.order^35 :=
      (Nat.mul_le_mul
        (CFSGTrialityGeckOriginalOrderUpper.original_order_le_power q hn)
        (CFSGTrialityGeckProperIndexOrderBudget.original_outer_card_le_power q)).trans_eq
          (by ring)
    calc
      (Nat.card (CFSG.Models.TrialityD4 q)*
          Nat.card (Outer (CFSG.Models.TrialityD4 q)))^3 ≤ (q.order^35)^3 :=
        Nat.pow_le_pow_left hc 3
      _ = q.order^105 := by rw [←pow_mul]
      _ ≤ q.order^198 := Nat.pow_le_pow_right (by omega) (by decide)
      _ ≤ 5^(2*q.order^4-1) :=
        FFourHeisenbergOrderCubeNumerics.field_power_cube_le q.order hq
  · rw [Nat.card_congr e.toEquiv]
    exact ((by decide : 1024 ≤ 3^24).trans (Nat.pow_le_pow_left hq 24)).trans
      (CFSGTrialityGeckOriginalOrderLower.original_card_lower q)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
