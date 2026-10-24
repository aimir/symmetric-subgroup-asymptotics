import SymmetricSubgroupAsymptotics.SLTwoSharpConjugacyClassBound
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneClassCube
import SymmetricSubgroupAsymptotics.RankOneSharpClassCubeNumerics

/-! The same literal SL2-to-original-PSL2 quotient transfers the sharper
trace count. Actual field exponents suffice to pay every component class
cube from field order seventeen onward. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankOneSharpClassCube
open PrimitiveSocleRawStructure CFSGPSLTwoRootCoordinates

theorem typeA_rank_one_class_card_le (q : CFSG.PrimePower) :
    Nat.card (ConjClasses (CFSG.Models.A 1 q)) ≤ q.order+4 := by
  have h := Nat.card_le_card_of_surjective (ConjClasses.map (projection (F:=q.Field)))
    (ConjClasses.map_surjective (projection_surjective (F:=q.Field)))
  exact h.trans (by simpa only [q.card_field] using SLTwoSharpConjugacyClassBound.class_card_le q.Field)

theorem component_class_cube (q : CFSG.PrimePower) (hq : 17 ≤ q.order) :
    (Nat.card (ConjClasses (CFSG.Models.A 1 q))*Nat.card (Outer (CFSG.Models.A 1 q)))^3 ≤
      5^((q.order+1)/2-1) := by
  let m := (q.order+1)/2
  have hqm : q.order ≤ 2*m := by dsimp only [m]; omega
  by_cases hbig : 23 ≤ q.order
  · have hm : 12 ≤ m := by dsimp only [m]; omega
    have ho : Nat.card (Outer (CFSG.Models.A 1 q)) ≤ m := by
      have h := CFSGTypeARankOneSharpComponentOrderCube.twice_outer_card_le_field q (by omega)
      omega
    have hc : Nat.card (ConjClasses (CFSG.Models.A 1 q))*
        Nat.card (Outer (CFSG.Models.A 1 q)) ≤ (2*m+4)*m :=
      Nat.mul_le_mul ((typeA_rank_one_class_card_le q).trans (by omega)) ho
    exact (Nat.pow_le_pow_left hc 3).trans (RankOneSharpClassCubeNumerics.class_cube_le m hm)
  · have he : q.exponent=1 := RankOneSharpClassCubeNumerics.exponent_one_of_small_order
      q.prime q.exponent q.prime_isPrime q.exponent_pos hq (show q.order ≤ 22 by omega)
    have ho : Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 2 := by
      have h := CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
      omega
    have hc : Nat.card (ConjClasses (CFSG.Models.A 1 q))*
        Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 4*m+8 := by
      have h := Nat.mul_le_mul (typeA_rank_one_class_card_le q) ho
      nlinarith
    have hm9 : 9 ≤ m := by dsimp only [m]; omega
    have hb := RankOneSharpOrderCubeNumerics.polynomial_tail 216 3 5 9 (by decide)
      (by norm_num : (10:ℕ)^3 ≤ 5*9^3)
      (by norm_num : (216:ℕ)*9^3 ≤ 5^8) m hm9
    have hc6 : 4*m+8 ≤ 6*m := by omega
    exact (Nat.pow_le_pow_left (hc.trans hc6) 3).trans (by convert hb using 1; ring)

end SymmetricSubgroupAsymptotics.CFSGTypeARankOneSharpClassCube
