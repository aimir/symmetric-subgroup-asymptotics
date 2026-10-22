import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Actual norm-one units in the literal quadratic extension. Their
order is bounded directly by cyclic-unit power kernels, without a
fixed-group or torus presentation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNormOneUnits
open CFSGSerreOrdinaryTwists

def normOneUnits (q : CFSG.PrimePower) : Subgroup (q.Extension 2)ˣ :=
  (powMonoidHom (q.order + 1) : (q.Extension 2)ˣ →* (q.Extension 2)ˣ).ker

theorem normOneUnits_card_le (q : CFSG.PrimePower) :
    Nat.card (normOneUnits q) ≤ q.order + 1 := by
  change Nat.card (powMonoidHom (q.order + 1) : (q.Extension 2)ˣ →* (q.Extension 2)ˣ).ker ≤ _
  rw [IsCyclic.card_powMonoidHom_ker]
  exact Nat.gcd_le_right _ (by omega)

theorem frobenius_eq_inv (q : CFSG.PrimePower) (u : normOneUnits q) :
    definingFieldAutomorphism q 2 (u.val : q.Extension 2) = (u.val : q.Extension 2)⁻¹ := by
  have hu : u.val ^ (q.order + 1) = 1 := u.property
  have h := congrArg (fun z : (q.Extension 2)ˣ => (z : q.Extension 2)) hu
  change (u.val : q.Extension 2) ^ (q.order + 1) = 1 at h
  rw [pow_succ] at h
  have hs : definingFieldAutomorphism q 2 (u.val : q.Extension 2) *
      (u.val : q.Extension 2) = 1 := by
    simpa only [definingFieldAutomorphism_apply] using h
  calc
    _ = definingFieldAutomorphism q 2 (u.val : q.Extension 2) *
        ((u.val : q.Extension 2) * (u.val : q.Extension 2)⁻¹) := by
      rw [mul_inv_cancel₀ (Units.ne_zero u.val), mul_one]
    _ = (definingFieldAutomorphism q 2 (u.val : q.Extension 2) *
        (u.val : q.Extension 2)) * (u.val : q.Extension 2)⁻¹ := by rw [mul_assoc]
    _ = _ := by rw [hs, one_mul]

end SymmetricSubgroupAsymptotics.CFSGTwistedDNormOneUnits
