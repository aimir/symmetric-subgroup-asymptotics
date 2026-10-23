import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoIndexUpper
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoOrderLower

/-! The remaining admissible rank-two unitary index square.  A coarse
polynomial orbit bound and the literal flag/torus order count suffice;
neither exact unitary order nor an isotropic-point census is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open PrimitiveSocleRawStructure

theorem twistedA_rank_two_leastIndex_square_lt (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.TwistedA 2 q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.TwistedA 2 q) := by
  have hu := twistedA_rank_two_index_mul_le q hq ell hell
  have ho := twistedA_rank_two_order_lower q hq
  have hk : 2 ≤ q.order - 1 := by omega
  have hqsub : q.order ^ 2 - 1 + 1 = q.order ^ 2 :=
    Nat.sub_add_cancel (by nlinarith)
  have hcrit : 3 * q.order ^ 2 < (q.order ^ 2 - 1) * (q.order - 1) ^ 2 := by
    have hs : 4 ≤ (q.order - 1) ^ 2 := by nlinarith
    have hm := Nat.mul_le_mul_left (q.order ^ 2 - 1) hs
    nlinarith
  have hs : ell ^ 2 * (q.order - 1) ^ 2 ≤ q.order ^ 6 * q.order ^ 2 := by
    calc
      _ = (ell * (q.order - 1)) ^ 2 := by ring
      _ ≤ (q.order ^ 4) ^ 2 := Nat.pow_le_pow_left hu 2
      _ = _ := by ring
  by_contra! hbad
  have hh : q.order ^ 6 * ((q.order ^ 2 - 1) * (q.order - 1) ^ 2) ≤
      q.order ^ 6 * (3 * q.order ^ 2) := by
    calc
      _ = (q.order ^ 6 * (q.order ^ 2 - 1)) * (q.order - 1) ^ 2 := by ring
      _ ≤ (3 * Nat.card (CFSG.Models.TwistedA 2 q)) * (q.order - 1) ^ 2 :=
        Nat.mul_le_mul_right _ ho
      _ ≤ (3 * ell ^ 2) * (q.order - 1) ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hbad)
      _ = 3 * (ell ^ 2 * (q.order - 1) ^ 2) := by ring
      _ ≤ 3 * (q.order ^ 6 * q.order ^ 2) := Nat.mul_le_mul_left 3 hs
      _ = _ := by ring
  have hpos : 0 < q.order ^ 6 := pow_pos (by omega) _
  exact hcrit.not_ge ((mul_le_mul_iff_right₀ hpos).mp hh)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
