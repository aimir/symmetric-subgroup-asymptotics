import SymmetricSubgroupAsymptotics.PrimitiveSocleModelProperClassCapacity
import SymmetricSubgroupAsymptotics.PrimitiveSocleSuzukiCompleteClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleReeGTwoCompleteClassBound

/-! Actual quadratic/torus and rectangular capacities pay the proper
subnormal extra exponent for every admissible Suzuki and small-Ree
parameter. The exact original model and both degree forms are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_suzuki_all_parameters
    (D : NonaffineData G X) (m : ℕ) (hm : 1 ≤ m)
    (e : D.Simple ≃* CFSG.Models.Suzuki m)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.Suzuki m) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.Suzuki m) := Finite.of_equiv D.Simple e.toEquiv
  have hN : Nat.card (CFSG.Models.Suzuki m)=
      SuzukiQuadraticTorusClassNumerics.orderBound (SuzukiQuadraticTorusClassNumerics.fieldOrder m) := by
    rw [CFSGSuzukiModelCardinality.model_card,CFSGSuzukiFieldParameters.field_card]
    rfl
  refine D.proper_subnormal_class_cube_le_of_model_order_capacity
    (CFSG.Models.Suzuki m) e (SuzukiQuadraticTorusClassNumerics.indexBound m)
    ((by decide : 3 ≤ 8).trans
      ((SuzukiQuadraticTorusClassNumerics.field_ge_eight m hm).trans
        (SuzukiQuadraticTorusClassNumerics.field_le_index m hm))) ?_ ?_ ?_ H hH hne
  · intro K hK
    have hi := CFSGSuzukiQuadraticTorusIndex.suzuki_quadratic_torus_le_proper_index m hm K hK
    change SuzukiQuadraticTorusClassNumerics.indexBound m ≤ K.index at hi
    exact hi
  · rw [hN]
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_left _
      (CFSGSuzukiOuterBound.outer_card_le m hm)) 3).trans
        (SuzukiQuadraticTorusClassNumerics.component_order_cube m hm)
  · rw [hN]
    have hq := SuzukiQuadraticTorusClassNumerics.field_ge_eight m hm
    have hq2 := Nat.pow_le_pow_left hq 2
    have h := Nat.mul_le_mul
      (Nat.mul_le_mul hq2 (Nat.sub_le_sub_right hq 1)) (Nat.add_le_add_right hq2 1)
    exact (by decide : 1024 ≤ 8^2*(8-1)*(8^2+1)).trans h

theorem NonaffineData.proper_subnormal_class_cube_le_of_reeGTwo_all_parameters
    (D : NonaffineData G X) (m : ℕ) (hm : 1 ≤ m)
    (e : D.Simple ≃* CFSG.Models.ReeG2 m)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.ReeG2 m) := Finite.of_equiv D.Simple e.toEquiv
  have hq : 27 ≤ 3^(2*m+1) :=
    Nat.pow_le_pow_right (by decide : 0<(3 : ℕ)) (by omega : 3 ≤ 2*m+1)
  have hb : 3 ≤ 3*3^(2*m+1) := by omega
  refine D.proper_subnormal_class_cube_le_of_model_order_capacity
    (CFSG.Models.ReeG2 m) e (3*3^(2*m+1)) hb
    (CFSGReeGTwoRectangularPermutationDegree.three_field_card_le_proper_index m hm)
    ?_ (CFSGReeGTwoOriginalOrderBounds.original_order_ge_1024 m hm) H hH hne
  have hc := Nat.pow_le_pow_left
    (CFSGReeGTwoOriginalOrderBounds.original_component_le_eighth m hm) 3
  calc
    _ ≤ ((3^(2*m+1))^8)^3 := hc
    _ = (3^(2*m+1))^24 := by rw [← pow_mul]
    _ ≤ 5^(3*3^(2*m+1)-1) :=
      ReeGTwoRectangularClassNumerics.field_power_cube_le (3^(2*m+1)) hq

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
