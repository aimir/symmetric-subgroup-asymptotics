import SymmetricSubgroupAsymptotics.SingletonExtensionExact
import SymmetricSubgroupAsymptotics.BinaryFamilies
import SymmetricSubgroupAsymptotics.MarkerZeroDefect

/-!
# The exact odd singleton branch of the binary error

Extend every intrinsic noncritical fixed-point-free binary subgroup by one
fixed point, allowing every original choice of that point.  Fixed-point
freeness makes the choice recoverable, so this is an exact physical count.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.NoncriticalBinaryOddSingleton

abbrev Family (N : ℕ) :=
  SingletonExtension.FinFamily (2*N)
    (fun H : NoncriticalBinarySubgroups N => H.val)

theorem card_eq (N : ℕ) :
    Nat.card (Family N) = (2*N+1) * Nat.card (NoncriticalBinarySubgroups N) := by
  simpa only [Nat.card_fin] using
    SingletonExtensionExact.card_family_eq
      (fun x : Fin (2*N+1) => finSuccEquiv' x) finSuccEquiv'_at
      (fun H : NoncriticalBinarySubgroups N => H.val)
      (fun _ _ h => Subtype.ext h)
      (fun H x => H.property.1.2 x)

theorem exactBenchmark_odd (N : ℕ) :
    exactBenchmark (2*N+1) = ((2*N+1).factorial : ℝ) *
      (binaryGaussianSum N : ℝ) * (analyticParityCoefficient 1 N : ℝ) := by
  unfold exactBenchmark
  rw [← analyticParityCoefficient_halfDegree (2*N+1)]
  have hh : halfDegree (2*N+1) = N := by unfold halfDegree; omega
  have hp : parity (2*N+1) = 1 := by unfold parity; omega
  rw [hh,hp]

/-- The physical singleton sector is exactly `alpha_N E_N` after the
approved benchmark normalization. -/
theorem normalized_card (N : ℕ) :
    (Nat.card (Family N) : ℝ) / exactBenchmark (2*N+1) =
      MarkerZeroDefect.alpha N * binaryErrorRatio N := by
  rw [card_eq, exactBenchmark_odd]
  unfold MarkerZeroDefect.alpha binaryErrorRatio
  rw [exactBenchmark_even]
  push_cast
  have hf : (((2*N).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hs : ((2*N+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hG : (binaryGaussianSum N : ℝ) ≠ 0 := by
    exact_mod_cast (binaryGaussianSum_pos N).ne'
  have hc : (criticalCoefficient N : ℝ) ≠ 0 := by
    exact_mod_cast (criticalCoefficient_pos N).ne'
  have hp : (analyticParityCoefficient 1 N : ℝ) ≠ 0 := by
    exact_mod_cast (analyticParityCoefficient_positive 1 N).ne'
  rw [show ((2*N+1).factorial : ℝ) = (2*N+1) * (2*N).factorial by
    rw [show 2*N+1 = (2*N)+1 by omega, Nat.factorial_succ]
    push_cast
    rfl]
  field_simp

end SymmetricSubgroupAsymptotics.NoncriticalBinaryOddSingleton

end
