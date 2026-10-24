import SymmetricSubgroupAsymptotics.SLTwoConjugacyClassBound
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneSharpComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneOrderThreshold
import SymmetricSubgroupAsymptotics.RankOneClassCubeNumerics

/-! The literal SL2 trace-class bound descends to the pinned original
PSL2 quotient. Its class-plus-outer cube is paid at the actual half-field
proper index for every field of size at least27. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankOneClassCube
open PrimitiveSocleRawStructure CFSGPSLTwoRootCoordinates

theorem typeA_rank_one_class_card_le (q : CFSG.PrimePower) :
    Nat.card (ConjClasses (CFSG.Models.A 1 q)) ≤ 2*q.order+4 := by
  have h := Nat.card_le_card_of_surjective (ConjClasses.map (projection (F:=q.Field)))
    (ConjClasses.map_surjective (projection_surjective (F:=q.Field)))
  exact h.trans (by simpa only [q.card_field] using SLTwoConjugacyClassBound.class_card_le q.Field)

theorem component_class_cube (q : CFSG.PrimePower) (hq : 27 ≤ q.order) :
    (Nat.card (ConjClasses (CFSG.Models.A 1 q))*Nat.card (Outer (CFSG.Models.A 1 q)))^3 ≤
      5^((q.order+1)/2-1) := by
  let m := (q.order+1)/2
  have hm : 14 ≤ m := by dsimp only [m]; omega
  have hqm : q.order ≤ 2*m := by dsimp only [m]; omega
  have ho : Nat.card (Outer (CFSG.Models.A 1 q)) ≤ m := by
    have h := CFSGTypeARankOneSharpComponentOrderCube.twice_outer_card_le_field q (by omega)
    omega
  have hc := RankOneClassCubeNumerics.component_le q.order m
    (Nat.card (ConjClasses (CFSG.Models.A 1 q))) (Nat.card (Outer (CFSG.Models.A 1 q)))
    (by omega) hqm (typeA_rank_one_class_card_le q) ho
  exact (Nat.pow_le_pow_left hc 3).trans (RankOneClassCubeNumerics.class_cube_le m hm)

end SymmetricSubgroupAsymptotics.CFSGTypeARankOneClassCube
