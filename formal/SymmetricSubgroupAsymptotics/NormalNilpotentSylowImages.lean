import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Sylow subgroups of an actual normal nilpotent subgroup give normal
subgroups of the original ambient group, with their actual orders. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.NormalNilpotentSylowImages

variable {G : Type} [Group G] [Finite G]
    (B : Subgroup G) [B.Normal] [Group.IsNilpotent B]
    {p : ℕ} [Fact p.Prime] (P : Sylow p B)

theorem image_normal : ((P : Subgroup B).map B.subtype).Normal := by
  letI : (P : Subgroup B).Normal := Sylow.normal_of_normalizerCondition
    (Group.normalizerCondition_of_isNilpotent (G := B)) P
  letI : (P : Subgroup B).Characteristic := Sylow.characteristic_of_normal P inferInstance
  infer_instance

theorem image_card : Nat.card ((P : Subgroup B).map B.subtype)=Nat.card P :=
  (Nat.card_congr ((P : Subgroup B).equivMapOfInjective
    B.subtype Subtype.coe_injective).toEquiv).symm

theorem image_isPGroup : IsPGroup p ((P : Subgroup B).map B.subtype) :=
  P.isPGroup'.map B.subtype

end SymmetricSubgroupAsymptotics.NormalNilpotentSylowImages
