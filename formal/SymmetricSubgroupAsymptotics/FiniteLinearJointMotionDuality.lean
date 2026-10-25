import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness
import Lean.Elab.Tactic.Omega

/-! A linear map from two copies of a finite-dimensional space to one
copy has kernel dimension equal to the original dimension plus the
dimension of its dual kernel. The resulting cardinal identity is the
linear ingredient for exact joint-motion counts; it assumes no group
action, orbit classification or character-theoretic formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteLinearJointMotionDuality

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

theorem finrank_kernel_eq_add_dual_kernel (T : (V × V) →ₗ[K] V) :
    Module.finrank K T.ker =
      Module.finrank K V + Module.finrank K T.dualMap.ker := by
  have hT := T.finrank_range_add_finrank_ker
  have hd := T.dualMap.finrank_range_add_finrank_ker
  rw [Module.finrank_prod] at hT
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range,
    Subspace.dual_finrank_eq] at hd
  omega

theorem card_kernel_eq_mul_dual_kernel (T : (V × V) →ₗ[K] V) :
    Nat.card T.ker = Nat.card V * Nat.card T.dualMap.ker := by
  have hT : Nat.card T.ker = Nat.card K ^ Module.finrank K T.ker :=
    Module.natCard_eq_pow_finrank (K := K) (V := T.ker)
  have hV : Nat.card V = Nat.card K ^ Module.finrank K V :=
    Module.natCard_eq_pow_finrank (K := K) (V := V)
  have hd : Nat.card T.dualMap.ker = Nat.card K ^ Module.finrank K T.dualMap.ker :=
    Module.natCard_eq_pow_finrank (K := K) (V := T.dualMap.ker)
  rw [hT, hV, hd, finrank_kernel_eq_add_dual_kernel, pow_add]

end SymmetricSubgroupAsymptotics.FiniteLinearJointMotionDuality
