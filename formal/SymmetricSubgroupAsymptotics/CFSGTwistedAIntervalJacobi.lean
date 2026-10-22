import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations
import Mathlib.Tactic.NormNum

/-! Jacobi/Serre identities for the original type-A interval-root span.
The middle-node cancellation is proved in the rational SOURCE Lie
algebra, before any natural realization is known injective. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalJacobi
variable {L : Type} [LieRing L] [Module ℚ L] [LieAlgebra ℚ L]

theorem outer_double_bracket (a b c : L) (hac : ⁅a, c⁆ = 0) :
    ⁅a, ⁅a, ⁅b, c⁆⁆⁆ = ⁅⁅a, ⁅a, b⁆⁆, c⁆ := by
  rw [leibniz_lie a b c, hac, lie_zero, add_zero,
    leibniz_lie a ⁅a, b⁆ c, hac, lie_zero, add_zero]

theorem outer_serre_inherits (a b c : L) (hac : ⁅a, c⁆ = 0)
    (hab : ⁅a, ⁅a, b⁆⁆ = 0) : ⁅a, ⁅a, ⁅b, c⁆⁆⁆ = 0 := by
  rw [outer_double_bracket a b c hac, hab, zero_lie]

theorem middle_bracket_zero (a b c : L) (hac : ⁅a, c⁆ = 0)
    (hba : ⁅b, ⁅b, a⁆⁆ = 0) (hbc : ⁅b, ⁅b, c⁆⁆ = 0) :
    ⁅b, ⁅a, ⁅b, c⁆⁆⁆ = 0 := by
  let X : L := ⁅⁅b, a⁆, ⁅b, c⁆⁆
  have hleft : ⁅b, ⁅b, ⁅a, c⁆⁆⁆ = 0 := by rw [hac, lie_zero, lie_zero]
  have hexp : ⁅b, ⁅b, ⁅a, c⁆⁆⁆ = X + X := by
    rw [leibniz_lie b a c, lie_add,
      leibniz_lie b ⁅b, a⁆ c, leibniz_lie b a ⁅b, c⁆,
      hba, hbc, zero_lie, lie_zero, zero_add, add_zero]
  have hsum : X + X = 0 := hexp.symm.trans hleft
  have htwo : (2 : ℚ) • X = 0 := by simpa only [two_smul] using hsum
  have hX : X = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  rw [leibniz_lie b a ⁅b, c⁆, hbc, lie_zero, add_zero]
  exact hX

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalJacobi
