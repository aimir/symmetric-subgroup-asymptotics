import SymmetricSubgroupAsymptotics.RankOneComponentOrderCubeNumerics
import SymmetricSubgroupAsymptotics.CFSGTypeAProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGPSLTwoLeastIndexOrder
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart

/-! Concrete original PSL2 order cubes at the proved half-field index.
No rank-one subgroup classification or class table is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankOneComponentOrderCube
open PrimitiveSocleRawStructure CFSGReduction

theorem component_le_of_field_le_twice (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A 1 q)] (m : ℕ) (hqm : q.order ≤ 2 * m) :
    Nat.card (CFSG.Models.A 1 q) * Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 64 * m ^ 5 := by
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hs : Nat.card (CFSG.Models.A 1 q) ≤ q.order ^ 4 :=
    typeA_order_le_matrix_power 1 q
  have ho : Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 2 * q.order :=
    (CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q).trans (Nat.mul_le_mul_left 2 hf)
  calc
    _ ≤ q.order ^ 4 * (2 * q.order) := Nat.mul_le_mul hs ho
    _ = 2 * q.order ^ 5 := by ring
    _ ≤ 2 * (2 * m) ^ 5 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hqm 5)
    _ = 64 * m ^ 5 := by ring

theorem component_order_cube (q : CFSG.PrimePower) (hq : 128 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.A 1 q)] :
    (Nat.card (CFSG.Models.A 1 q) * Nat.card (Outer (CFSG.Models.A 1 q))) ^ 3 ≤
      5 ^ ((q.order + 1) / 2 - 1) := by
  have hm : 64 ≤ (q.order + 1) / 2 := by omega
  have hqm : q.order ≤ 2 * ((q.order + 1) / 2) := by omega
  exact (Nat.pow_le_pow_left (component_le_of_field_le_twice q _ hqm) 3).trans
    (RankOneComponentOrderCubeNumerics.order_cube_le _ hm)

theorem order_ge_1024 (q : CFSG.PrimePower) (hq : 128 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.A 1 q)] : 1024 ≤ Nat.card (CFSG.Models.A 1 q) := by
  obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.A 1 q)
  have hfield : q.order ≤ 2 * ell := by
    simpa only [q.card_field] using
      CFSGPSLTwoGeometry.field_card_le_twice_leastProperIndex (F := q.Field) ell hell
  have hlo : 32 ≤ ell := by omega
  have hs := CFSGPSLTwoGeometry.leastProperIndex_square_lt_card (F := q.Field)
    (by rw [q.card_field]; omega) ell hell
  change ell ^ 2 < Nat.card (CFSG.Models.A 1 q) at hs
  have hp := Nat.pow_le_pow_left hlo 2
  norm_num only [Nat.reducePow] at hp
  omega

end SymmetricSubgroupAsymptotics.CFSGTypeARankOneComponentOrderCube
