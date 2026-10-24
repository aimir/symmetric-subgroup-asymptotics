import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGSuzukiQuadraticTorusIndex
import SymmetricSubgroupAsymptotics.CFSGSuzukiModelCardinality
import SymmetricSubgroupAsymptotics.CFSGSuzukiOuterBound
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.SuzukiQuadraticTorusClassNumerics

/-! The actual quadratic/torus index pays the original Suzuki component
order cube at every parameter. Every original socle factor, subgroup
and both raw primitive degree forms are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction SuzukiQuadraticTorusClassNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_suzuki_allDegrees
    (D : NonaffineData G X) (m : ℕ) (hm : 1 ≤ m)
    (e : D.Simple ≃* CFSG.Models.Suzuki m) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.Suzuki m) := e.symm.isSimpleGroup
  have hN : Nat.card (CFSG.Models.Suzuki m) = orderBound (fieldOrder m) := by
    rw [CFSGSuzukiModelCardinality.model_card, CFSGSuzukiFieldParameters.field_card]
    rfl
  refine D.subgroup_class_cube_le_of_component_order_cube (indexBound m) ?_ ?_ ?_ ?_ H
  · exact (by decide : 3 ≤ 8).trans ((field_ge_eight m hm).trans (field_le_index m hm))
  · intro K hK
    have hproper : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGSuzukiQuadraticTorusIndex.suzuki_quadratic_torus_le_proper_index
      m hm (K.map e.toMonoidHom) hproper
    have hindex : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
    change indexBound m ≤ (K.map e.toMonoidHom).index at hi
    exact hi.trans_eq hindex
  · rw [Nat.card_congr e.toEquiv, outer_card_congr e, hN]
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_left _
      (CFSGSuzukiOuterBound.outer_card_le m hm)) 3).trans (component_order_cube m hm)
  · rw [Nat.card_congr e.toEquiv, hN]
    have hq := field_ge_eight m hm
    have hq2 := Nat.pow_le_pow_left hq 2
    have h := Nat.mul_le_mul
      (Nat.mul_le_mul hq2 (Nat.sub_le_sub_right hq 1)) (Nat.add_le_add_right hq2 1)
    exact (by decide : 1024 ≤ 8^2*(8-1)*(8^2+1)).trans h

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
