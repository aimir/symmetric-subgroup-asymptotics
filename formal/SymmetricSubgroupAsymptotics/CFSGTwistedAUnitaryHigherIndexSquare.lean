import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectivePointIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveOrderLower
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! The least-index square inequality for every original unitary model
of rank at least four. The point count is deliberately coarse; the
literal opposite Sylow product already supplies the required margin. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices PrimitiveSocleRawStructure

theorem unitaryNaturalPoints_card_le (q : CFSG.PrimePower) (r : ℕ) :
    Nat.card (unitaryNaturalPoints q r) ≤ q.order ^ (2 * r + 1) := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hc : Nat.card (unitaryNaturalPoints q r) * (q.order ^ 2 - 1) =
      q.order ^ (2 * (r + 1)) - 1 := by
    simpa only [Nat.card_fun, Nat.card_fin, extension_two_card, ← pow_mul] using
      (Projectivization.card (q.Extension 2) (Fin (r + 1) → q.Extension 2)).symm
  have hd : q.order ≤ q.order ^ 2 - 1 := by nlinarith [Nat.sub_add_cancel (by nlinarith : 1 ≤ q.order ^ 2)]
  have he : 2 * (r + 1) = (2 * r + 1) + 1 := by omega
  have hpow : q.order ^ (2 * (r + 1)) = q.order ^ (2 * r + 1) * q.order := by
    rw [he, pow_succ]
  rw [hpow] at hc
  by_contra hn
  have hstrict : q.order ^ (2 * r + 1) + 1 ≤ Nat.card (unitaryNaturalPoints q r) := by omega
  have hm := Nat.mul_le_mul hstrict hd
  rw [hc] at hm
  nlinarith [Nat.sub_le (q.order ^ (2 * r + 1) * q.order) 1]

theorem twistedA_higher_leastIndex_square_lt (q : CFSG.PrimePower) (s ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedA (s + 4) q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.TwistedA (s + 4) q) := by
  obtain ⟨H, hH, hindex⟩ := twistedA_shifted_exists_proper_subgroup_point_index q (s + 1)
  have hb : ell ≤ q.order ^ (2 * (s + 4) + 1) :=
    (hell.2 H hH).trans (hindex.trans (unitaryNaturalPoints_card_le q (s + 4)))
  have hq : 1 < q.order := lt_of_lt_of_le (by decide : 1 < 2)
    (q.prime_isPrime.two_le.trans (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime))
  have he : (2 * (s + 4) + 1) * 2 < (s + 4) * (s + 5) := by nlinarith
  have ho := twistedA_shifted_order_lower_exp q (s + 1)
  calc
    ell ^ 2 ≤ (q.order ^ (2 * (s + 4) + 1)) ^ 2 := Nat.pow_le_pow_left hb 2
    _ = q.order ^ ((2 * (s + 4) + 1) * 2) := (pow_mul _ _ _).symm
    _ < q.order ^ ((s + 4) * (s + 5)) := pow_lt_pow_right₀ hq he
    _ ≤ Nat.card (CFSG.Models.TwistedA (s + 4) q) := ho

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
