import SymmetricSubgroupAsymptotics.CFSGTypeARankOneSharpClassCube
import SymmetricSubgroupAsymptotics.CFSGPSLTwoLeastIndexOrder

/-! One polynomial tail pays the actual PSL2 class/outer packet from
field order 51. The original half-field proper-index bound is retained;
no assertion about the smaller fields or their actions is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoScaledClassPacket
open PrimitiveSocleRawStructure

theorem scaled_quadratic_cube_tail (n : ℕ) (hn : 26 ≤ n) :
    25*(4*n^2)^3 ≤ 3^n := by
  have h := RankOneSharpOrderCubeNumerics.polynomial_tail 1600 6 3 26
    (by decide) (by decide +kernel) (by decide +kernel) n hn
  have he : 25*(4*n^2)^3=1600*n^6 := by ring
  rw [he]
  exact h.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le n 1))

theorem scaled_class_cube_le_proper_index (q : CFSG.PrimePower) (hq : 51 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.A 1 q)]
    (K : Subgroup (CFSG.Models.A 1 q)) (hK : K ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.A 1 q))*
      Nat.card (Outer (CFSG.Models.A 1 q)))^3 ≤ 3^K.index := by
  have hi : q.order ≤ 2*K.index := by
    simpa only [q.card_field] using
      CFSGPSLTwoGeometry.field_card_le_twice_proper_index (F := q.Field) K hK
  have hn : 26 ≤ K.index := by omega
  have ho : Nat.card (Outer (CFSG.Models.A 1 q)) ≤ K.index := by
    have hh := CFSGTypeARankOneSharpComponentOrderCube.twice_outer_card_le_field q (by omega)
    omega
  have hc : Nat.card (ConjClasses (CFSG.Models.A 1 q)) ≤ 2*K.index+4 :=
    (CFSGTypeARankOneSharpClassCube.typeA_rank_one_class_card_le q).trans (by omega)
  have hp : (2*K.index+4)*K.index ≤ 4*K.index^2 := by nlinarith
  exact (Nat.mul_le_mul_left 25
    (Nat.pow_le_pow_left ((Nat.mul_le_mul hc ho).trans hp) 3)).trans
      (scaled_quadratic_cube_tail K.index hn)

end SymmetricSubgroupAsymptotics.CFSGPSLTwoScaledClassPacket
