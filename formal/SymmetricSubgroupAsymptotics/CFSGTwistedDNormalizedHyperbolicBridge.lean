import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPolePolar
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticShell

/-! A normalized hyperbolic pair and a third nonzero singular vector
have a common nonorthogonal singular vector whenever the third vector
is orthogonal to at least one axis. The actual smaller norm-plane shell
makes this valid in the nonsplit rank-two residual case and over F2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizedHyperbolicBridge
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedTailLinear
open CFSGTwistedDFixedPolePolar CFSGTwistedDFixedQuadraticShell CFSGTwistedA2FixedField

theorem exists_bridge (n : ℕ) (q : CFSG.PrimePower) (t : fixedSpace (n + 1) q)
    (ht : t ≠ 0) (htQ : fixedQuadraticForm (n + 1) q t = 0)
    (havoid : positiveHead n q t = 0 ∨ negativeHead n q t = 0) :
    ∃ d : fixedSpace (n + 1) q, fixedQuadraticForm (n + 1) q d = 0 ∧
      positiveHead n q d = 1 ∧ negativeHead n q d = 1 ∧
      (fixedQuadraticForm (n + 1) q).polarBilin t d ≠ 0 := by
  let a := positiveHead n q t
  let b := negativeHead n q t
  let z := tailLinear n q t
  have hab : a * b = 0 := by
    rcases havoid with ha | hb
    · change a = 0 at ha
      rw [ha, zero_mul]
    · change b = 0 at hb
      rw [hb, mul_zero]
  have hzQ : fixedQuadraticForm n q z = 0 := by
    have h := quadratic_coordinates n q t
    change fixedQuadraticForm (n + 1) q t = a * b + fixedQuadraticForm n q z at h
    rw [htQ, hab, zero_add] at h
    exact h.symm
  have hchoice : ∃ z' : fixedSpace n q, fixedQuadraticForm n q z' = -1 ∧
      a + b + (fixedQuadraticForm n q).polarBilin z z' ≠ 0 := by
    by_cases hz : z = 0
    · obtain ⟨z', hz', _⟩ := exists_shell_at_axis n q (-1) 0
      refine ⟨z', hz', ?_⟩
      have hsum : a + b ≠ 0 := by
        intro he
        have hboth : a = 0 ∧ b = 0 := by
          rcases mul_eq_zero.mp hab with ha | hb
          · exact ⟨ha, by simpa only [ha, zero_add] using he⟩
          · exact ⟨by simpa only [hb, add_zero] using he, hb⟩
        apply ht
        apply (poleEquiv n q).injective
        have hcoord : poleEquiv n q t = 0 := by
          change (a, (z, b)) = 0
          rw [hboth.1, hboth.2, hz]
          rfl
        exact hcoord.trans (map_zero _).symm
      simpa only [hz, map_zero, LinearMap.zero_apply, add_zero] using hsum
    · obtain ⟨z', hz', hB⟩ := exists_quadratic_polar_values n q z hz hzQ
        (-1) (1 - (a + b))
      refine ⟨z', hz', ?_⟩
      rw [hB]
      have he : a + b + (1 - (a + b)) = (1 : fixedField q) := by ring
      rw [he]
      exact one_ne_zero
  obtain ⟨z', hz', hB⟩ := hchoice
  let d := (poleEquiv n q).symm (1, (z', 1))
  refine ⟨d, ?_, positiveHead_inv n q 1 1 z', negativeHead_inv n q 1 1 z', ?_⟩
  · rw [quadratic_inv, hz', one_mul, add_neg_cancel]
  · change (fixedQuadraticForm (n + 1) q).polarBilin t
      ((poleEquiv n q).symm (1, (z', 1))) ≠ 0
    rw [polar_coordinates, positiveHead_inv, negativeHead_inv, tailLinear_inv,
      one_mul, mul_one]
    exact hB

end SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizedHyperbolicBridge
