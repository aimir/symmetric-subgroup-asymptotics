import SymmetricSubgroupAsymptotics.External.CFSG.Models.Chevalley
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Actual divided-power identities on the pinned integral Serre lattice.
These do not require a finite-type basis or any unproved nilpotence bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreDividedPowers
open CFSG.Models.Chevalley

private theorem factorial_scalar_mul (k l : ℕ) :
    (k.factorial : ℚ)⁻¹ * (l.factorial : ℚ)⁻¹ =
      ((k + l).choose l : ℚ) * ((k + l).factorial : ℚ)⁻¹ := by
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hl : (l.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
  have hkl : ((k + l).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + l)
  have hc : ((k + l).choose l : ℚ) * (k.factorial : ℚ) * (l.factorial : ℚ) =
      ((k + l).factorial : ℚ) := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial k l
  field_simp [hk, hl, hkl]
  nlinarith [hc]

/-- The factorial identity holds for the actual powers of any rational
linear endomorphism; no root-vector or representation premise is needed. -/
theorem rational_dividedPower_mul {V : Type*} [AddCommGroup V] [Module ℚ V]
    (D : Module.End ℚ V) (k l : ℕ) :
    ((k.factorial : ℚ)⁻¹ • D ^ k) * ((l.factorial : ℚ)⁻¹ • D ^ l) =
      ((k + l).choose l : ℚ) • (((k + l).factorial : ℚ)⁻¹ • D ^ (k + l)) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add, factorial_scalar_mul]
  rw [Nat.add_comm l k, Nat.choose_symm_add]

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

@[simp] theorem dividedPower_zero (negative : Bool) (i : Fin n) :
    dividedPower A negative i 0 = 1 := by
  ext x
  simp [dividedPower]

theorem dividedPower_mul (negative : Bool) (i : Fin n) (k l : ℕ) :
    dividedPower A negative i k * dividedPower A negative i l =
      (k + l).choose l • dividedPower A negative i (k + l) := by
  ext x
  have h := congrArg (fun f : Module.End ℚ (RationalLie A) => f x)
    (rational_dividedPower_mul
      (LieAlgebra.ad ℚ (RationalLie A) (rootVector A negative i)) k l)
  simpa only [dividedPower, Module.End.mul_apply, LinearMap.smul_apply,
    Nat.cast_smul_eq_nsmul] using h

@[simp] theorem integralOperator_zero (negative : Bool) (i : Fin n) :
    integralOperator A negative i 0 = 1 := by
  ext x
  change dividedPower A negative i 0 x.val = x.val
  rw [dividedPower_zero]
  rfl

/-- Composition in the actual integral lattice has the genuine integral
binomial coefficient. Denominators have been eliminated before base change. -/
theorem integralOperator_mul (negative : Bool) (i : Fin n) (k l : ℕ) :
    integralOperator A negative i k * integralOperator A negative i l =
      (k + l).choose l • integralOperator A negative i (k + l) := by
  ext x
  change dividedPower A negative i k (dividedPower A negative i l x.val) =
    (k + l).choose l • dividedPower A negative i (k + l) x.val
  exact congrArg (fun f : Module.End ℤ (RationalLie A) => f x.val)
    (dividedPower_mul A negative i k l)

theorem integralOperator_commute (negative : Bool) (i : Fin n) (k l : ℕ) :
    Commute (integralOperator A negative i k) (integralOperator A negative i l) := by
  show integralOperator A negative i k * integralOperator A negative i l =
    integralOperator A negative i l * integralOperator A negative i k
  rw [integralOperator_mul, integralOperator_mul]
  simpa only [Nat.add_comm l k] using congrArg
    (fun c : ℕ => c • integralOperator A negative i (k + l))
    (Nat.choose_symm_add (a := l) (b := k))

variable (K : Type) [Field K]

theorem baseChangedIntegralOperator_mul (negative : Bool) (i : Fin n) (k l : ℕ) :
    (integralOperator A negative i k).baseChange K *
      (integralOperator A negative i l).baseChange K =
      (k + l).choose l • (integralOperator A negative i (k + l)).baseChange K := by
  have h := congrArg (fun f : Module.End ℤ (integralLattice A) =>
      (Module.End.baseChangeHom ℤ K (integralLattice A)) f)
    (integralOperator_mul A negative i k l)
  simpa only [map_mul, map_nsmul] using h

/-- The zero root parameter gives the identity on the actual reduced
integral lattice, in every characteristic. -/
@[simp] theorem rootOperator_zero (negative : Bool) (i : Fin n) :
    rootOperator A K negative i 0 = 1 := by
  simp [rootOperator, Finset.sum_range_succ, integralOperator_zero]

end SymmetricSubgroupAsymptotics.CFSGSerreDividedPowers
