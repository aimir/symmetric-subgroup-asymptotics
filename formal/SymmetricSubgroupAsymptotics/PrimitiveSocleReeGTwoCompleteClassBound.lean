import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGReeGTwoRectangularPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOrderBounds
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The actual rectangular index bound pays every original ReeG2
primitive component at every parameter. All socle factors, subgroups
and both raw primitive degree forms remain literal. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_reeGTwo_allDegrees
    (D : NonaffineData G X) (m : ℕ) (hm : 1 ≤ m)
    (e : D.Simple ≃* CFSG.Models.ReeG2 m) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := e.symm.isSimpleGroup
  have hq : 27 ≤ 3^(2*m+1) :=
    Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) (by omega : 3 ≤ 2*m+1)
  have hb : 3 ≤ 3*3^(2*m+1) := by omega
  refine D.subgroup_class_cube_le_of_component_order_cube (3*3^(2*m+1)) hb ?_ ?_ ?_ H
  · intro K hK
    have hproper : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGReeGTwoRectangularPermutationDegree.three_field_card_le_proper_index
      m hm (K.map e.toMonoidHom) hproper
    exact hi.trans_eq (K.index_map_equiv e)
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    have hc := Nat.pow_le_pow_left
      (CFSGReeGTwoOriginalOrderBounds.original_component_le_eighth m hm) 3
    calc
      _ ≤ ((3^(2*m+1))^8)^3 := hc
      _ = (3^(2*m+1))^24 := by rw [←pow_mul]
      _ ≤ 5^(3*3^(2*m+1)-1) :=
        ReeGTwoRectangularClassNumerics.field_power_cube_le (3^(2*m+1)) hq
  · rw [Nat.card_congr e.toEquiv]
    exact CFSGReeGTwoOriginalOrderBounds.original_order_ge_1024 m hm

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
