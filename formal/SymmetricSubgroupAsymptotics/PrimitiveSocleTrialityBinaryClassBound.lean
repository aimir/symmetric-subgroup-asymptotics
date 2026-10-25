import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryRegularModuleIndex
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOrderLower
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Binary triality on the original primitive component, using its actual
regular-tensor index. Every socle factor and both degree forms remain. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_triality_binary
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* CFSG.Models.TrialityD4 q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.TrialityD4 q) :=
    fun h=>D.noncommutative ((isMulCommutative_congr e).mpr h)
  refine D.subgroup_class_cube_le_of_component_order_cube 64 (by decide) ?_ ?_ ?_ H
  · intro K hK
    have hproper : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGTrialityBinaryRegularModuleIndex.typeTriality_binary_regular_le_proper_index
      q hq (K.map e.toMonoidHom) hproper
    exact hi.trans_eq (K.index_map_equiv e)
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    have horder : Nat.card (CFSG.Models.TrialityD4 q)*
        Nat.card (Outer (CFSG.Models.TrialityD4 q)) ≤ q.order^35 :=
      (Nat.mul_le_mul
        (CFSGTrialityGeckOriginalOrderUpper.original_order_le_power q hn)
        (CFSGTrialityGeckProperIndexOrderBudget.original_outer_card_le_power q)).trans_eq
          (by ring)
    have hc := Nat.pow_le_pow_left horder 3
    have hnum : (q.order^35)^3≤5^(64-1) := by rw [hq]; decide +kernel
    exact hc.trans hnum
  · rw [Nat.card_congr e.toEquiv]
    have hlow := CFSGTrialityGeckOriginalOrderLower.original_card_lower q
    have hnum : 1024≤q.order^24 := by rw [hq]; decide
    exact hnum.trans hlow

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
