import Mathlib.Algebra.Group.Commute.Basic

/-! Four interleaved factors separate into two actual words when all
cross factors commute. No commutativity within either word is assumed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGCommutingPairedWord
variable {G : Type*} [Monoid G]

theorem four_pairs (a b : Fin 4 → G) (hc : ∀ i j, Commute (a i) (b j)) :
    (a 0 * b 0) * (a 1 * b 1) * (a 2 * b 2) * (a 3 * b 3) =
      (a 0 * a 1 * a 2 * a 3) * (b 0 * b 1 * b 2 * b 3) := by
  calc
    _ = (a 0 * a 1) * (b 0 * b 1) * (a 2 * b 2) * (a 3 * b 3) := by
      rw [(hc 1 0).symm.mul_mul_mul_comm]
    _ = (a 0 * a 1 * a 2) * (b 0 * b 1 * b 2) * (a 3 * b 3) := by
      rw [((hc 2 0).mul_right (hc 2 1)).symm.mul_mul_mul_comm]
    _ = _ := (((hc 3 0).mul_right (hc 3 1)).mul_right (hc 3 2)).symm.mul_mul_mul_comm _ _

end SymmetricSubgroupAsymptotics.CFSGCommutingPairedWord
