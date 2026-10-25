import SymmetricSubgroupAsymptotics.CFSGUnitaryTenHeadIndex
import SymmetricSubgroupAsymptotics.CFSGUnitaryTenHeadOuter
import SymmetricSubgroupAsymptotics.CFSGUnitaryFrameOrderUpper
import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound

/-! The ten bounded unitary parameters share one actual order, index
and class-equation proof. No class census, supplied capacity or group
recognition is used. The scalar table is applied only after its three
ceilings have been proved for the same original projective model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryTenHeadScaledClassPacket
open PrimitiveSocleRawStructure CFSGTwistedAUnitaryCoordinates
open UnitaryTenHeadScaledFrameNumerics

theorem scaled_class_cube_le_proper_index (j : Fin 10) (q : CFSG.PrimePower)
    (hq : q.order=(parameters j).2)
    [IsSimpleGroup (CFSG.Models.TwistedA (parameters j).1 q)]
    [Finite (CFSG.Models.TwistedA (parameters j).1 q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedA (parameters j).1 q))
    (H : Subgroup (CFSG.Models.TwistedA (parameters j).1 q)) (hH : H≠⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.TwistedA (parameters j).1 q))*
      Nat.card (Outer (CFSG.Models.TwistedA (parameters j).1 q)))^3 ≤ 3^H.index := by
  have hp := parameter_admissible j
  have hsmall : (parameters j).1=2 → q.order≠2 := by omega
  have horder : Nat.card (CFSG.Models.TwistedA (parameters j).1 q) ≤ orderCeiling j := by
    have hh := twistedA_admissible_order_mul_normOne_le_frame
      (parameters j).1 hp.1 q hsmall
    rw [Nat.mul_comm] at hh
    have hdiv := (Nat.le_div_iff_mul_le (by omega : 0<q.order+1)).mpr hh
    simpa only [orderCeiling,hq] using hdiv
  have hz : Subgroup.center (CFSG.Models.TwistedA (parameters j).1 q)=⊥ := by
    rcases (inferInstance :
      (Subgroup.center (CFSG.Models.TwistedA (parameters j).1 q)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hn (Subgroup.center_eq_top_iff.mp h)).elim
  have hindex : ∀ K : Subgroup (CFSG.Models.TwistedA (parameters j).1 q), K≠⊤ →
      indexFloor j ≤ K.index := fun K hK => CFSGUnitaryTenHeadIndex.proper_index_floor j q hq K hK
  have hclasses := CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
    (indexFloor j) (indexFloor_pos j) hz hindex
  apply scaled_capacity_of_bounds j
    (Nat.card (ConjClasses (CFSG.Models.TwistedA (parameters j).1 q)))
    (Nat.card (Outer (CFSG.Models.TwistedA (parameters j).1 q))) H.index
  · exact hclasses.trans (Nat.add_le_add_right (Nat.div_le_div_right horder) 1)
  · exact CFSGUnitaryTenHeadOuter.outer_card_le j (parameters j).1 q
      (by rw [hq]) hn
  · exact hindex H hH

end SymmetricSubgroupAsymptotics.CFSGUnitaryTenHeadScaledClassPacket
