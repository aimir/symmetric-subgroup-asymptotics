import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.FieldTheory.Finite.Basic

/-! Scalar rigidity for two actual p-elements in defining characteristic.
It uses their genuine p-power orders and injectivity of Frobenius, not a
trace/dimension argument which could fail when p divides the dimension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMatrixSupport

theorem scalar_eq_one_of_p_powers {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    [Nonempty I] (p : ℕ) [Fact p.Prime] [CharP K p]
    (A B : (Matrix I I K)ˣ) (a b : ℕ) (c : K)
    (hA : A ^ (p ^ a) = 1) (hB : B ^ (p ^ b) = 1)
    (hs : (A : Matrix I I K) = c • (B : Matrix I I K)) : c = 1 := by
  have hAp : A ^ (p ^ (a + b)) = 1 := by
    rw [pow_add, pow_mul, hA, one_pow]
  have hBp : B ^ (p ^ (a + b)) = 1 := by
    rw [Nat.add_comm a b, pow_add, pow_mul, hB, one_pow]
  have haM : (A : Matrix I I K) ^ (p ^ (a + b)) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hAp
  have hbM : (B : Matrix I I K) ^ (p ^ (a + b)) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hBp
  rw [hs, smul_pow, hbM] at haM
  let i : I := Classical.choice inferInstance
  have hc := congrArg (fun M : Matrix I I K => M i i) haM
  have hp : c ^ (p ^ (a + b)) = 1 := by
    simpa only [Matrix.smul_apply, Matrix.one_apply, if_true, smul_eq_mul, mul_one] using hc
  apply iterateFrobenius_inj K p (a + b)
  simpa only [iterateFrobenius_def, one_pow] using hp

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMatrixSupport
