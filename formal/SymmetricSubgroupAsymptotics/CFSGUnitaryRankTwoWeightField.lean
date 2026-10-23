import SymmetricSubgroupAsymptotics.CFSGInvolutiveScalarWeights
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldLargeSubfield
import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAPairedFixedRoots

/-! The actual first-layer rank-two torus weights generate the whole
quadratic field, including q=3. This supplies field reconstruction from
the literal torus action without a Hermitian-point catalogue. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGInvolutiveScalarWeights

def rankTwoFirstWeightHom (q : CFSG.PrimePower) : (q.Extension 2)ˣ →* (q.Extension 2)ˣ :=
  weightHom (definingFieldAutomorphism q 2)

theorem rankTwoFirstWeightHom_val (q : CFSG.PrimePower) (z : (q.Extension 2)ˣ) :
    (rankTwoFirstWeightHom q z : q.Extension 2) =
      CFSGTwistedA2DiagonalTorus.firstWeight (q.Extension 2) (definingFieldAutomorphism q 2) z :=
  weightHom_val (definingFieldAutomorphism q 2) z

theorem rankTwoFirstWeight_range_card_square_gt (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Nat.card (q.Extension 2) < Nat.card (rankTwoFirstWeightHom q).range ^ 2 := by
  have hc := range_card_mul_gcd_lower (definingFieldAutomorphism q 2)
    (fun x => extension_two_pow_twice q x)
  rw [extension_two_card] at hc
  change q.order ^ 2 - 1 ≤ (q.order ^ 2 - 1).gcd 3 * Nat.card (rankTwoFirstWeightHom q).range at hc
  rw [extension_two_card]
  by_cases hthree : q.order = 3
  · rw [hthree] at hc ⊢
    norm_num at hc ⊢
    nlinarith
  · have hg : (q.order ^ 2 - 1).gcd 3 ≤ 3 := Nat.gcd_le_right _ (by decide)
    have hm := hc.trans (Nat.mul_le_mul_right (Nat.card (rankTwoFirstWeightHom q).range) hg)
    have hsub := Nat.sub_add_cancel (show 1 ≤ q.order ^ 2 by nlinarith)
    have hq4 : 4 ≤ q.order := by omega
    have hmul := Nat.mul_le_mul_left q.order hq4
    have hlarge : q.order < Nat.card (rankTwoFirstWeightHom q).range := by nlinarith
    nlinarith

theorem rankTwoFirstWeight_generates_field (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Subfield.closure ((fun u : (q.Extension 2)ˣ => (u : q.Extension 2)) ''
      ((rankTwoFirstWeightHom q).range : Set (q.Extension 2)ˣ)) = ⊤ :=
  CFSGFiniteFieldLargeSubfield.closure_unit_subgroup_eq_top _
    (rankTwoFirstWeight_range_card_square_gt q hq)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
