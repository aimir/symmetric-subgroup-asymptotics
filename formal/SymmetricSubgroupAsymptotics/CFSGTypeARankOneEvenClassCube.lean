import SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenOuterBound
import SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenPermutationDegree
import SymmetricSubgroupAsymptotics.EvenRankOneClassCubeNumerics
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneSmallPrimeClassCube

/-! The actual characteristic-two torus pays both the stronger proper
index and the exact field-exponent outer bound. A single binary
numerical theorem closes all original rank-one fields of size at least8. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankOneEvenClassCube
open PrimitiveSocleRawStructure

theorem exponent_ge_three (q : CFSG.PrimePower) (hp : q.prime=2) (hq : 8 ≤ q.order) :
    3 ≤ q.exponent := by
  by_contra h
  have hb := Nat.pow_le_pow_right (by decide : 0<2) (by omega : q.exponent ≤ 2)
  have horder : q.order=2^q.exponent := by simp only [CFSG.PrimePower.order,hp]
  norm_num at hb
  omega

theorem component_class_cube (q : CFSG.PrimePower) (hp : q.prime=2) (hq : 8 ≤ q.order) :
    (Nat.card (ConjClasses (CFSG.Models.A 1 q))*Nat.card (Outer (CFSG.Models.A 1 q)))^3 ≤
      5^(q.order-1) := by
  have horder : q.order=2^q.exponent := by simp only [CFSG.PrimePower.order,hp]
  have hc := Nat.mul_le_mul (CFSGTypeARankOneSharpClassCube.typeA_rank_one_class_card_le q)
    (CFSGPSLTwoEvenOuterBound.typeA_rank_one_outer_card q hp)
  have hb := Nat.pow_le_pow_left hc 3
  rw [horder] at hb ⊢
  exact hb.trans (EvenRankOneClassCubeNumerics.class_cube_le q.exponent
    (exponent_ge_three q hp hq))

end SymmetricSubgroupAsymptotics.CFSGTypeARankOneEvenClassCube
