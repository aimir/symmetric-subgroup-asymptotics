import SymmetricSubgroupAsymptotics.CFSGSerreRootOperatorInvertible
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! A field automorphism acts semilinearly on the original base-changed
integral lattice. Every original root polynomial is intertwined with the
same polynomial at the transported parameter, in all characteristics. -/
set_option autoImplicit false
noncomputable section
open scoped Classical TensorProduct BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreField
open CFSG.Models.Chevalley
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    (σ : K ≃+* K)

def tensorEquiv : Space A K ≃ₗ[ℤ] Space A K :=
  TensorProduct.congr σ.toAddEquiv.toIntLinearEquiv (LinearEquiv.refl ℤ (integralLattice A))

@[simp] theorem tensorEquiv_tmul (a : K) (v : integralLattice A) :
    tensorEquiv A K σ (a ⊗ₜ[ℤ] v) = σ a ⊗ₜ[ℤ] v := rfl

theorem tensorEquiv_smul (a : K) (x : Space A K) :
    tensorEquiv A K σ (a • x) = σ a • tensorEquiv A K σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul b v =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, tensorEquiv_tmul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

local instance cfsgSerreFieldSigmaInvPair :
    RingHomInvPair σ.toRingHom σ.symm.toRingHom := RingHomInvPair.of_ringEquiv σ

local instance cfsgSerreFieldSigmaSymmInvPair :
    RingHomInvPair σ.symm.toRingHom σ.toRingHom := RingHomInvPair.of_ringEquiv_symm σ

def semilinearEquiv : Space A K ≃ₛₗ[σ.toRingHom] Space A K where
  __ := (tensorEquiv A K σ).toAddEquiv
  map_smul' := tensorEquiv_smul A K σ

@[simp] theorem semilinearEquiv_tmul (a : K) (v : integralLattice A) :
    semilinearEquiv A K σ (a ⊗ₜ[ℤ] v) = σ a ⊗ₜ[ℤ] v := rfl

theorem semilinearEquiv_integralOperator (negative : Bool) (i : Fin n) (k : ℕ)
    (x : Space A K) :
    semilinearEquiv A K σ ((integralOperator A negative i k).baseChange K x) =
      (integralOperator A negative i k).baseChange K (semilinearEquiv A K σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a v => simp only [LinearMap.baseChange_tmul, semilinearEquiv_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem semilinearEquiv_rootOperator (negative : Bool) (i : Fin n) (t : K)
    (x : Space A K) :
    semilinearEquiv A K σ (rootOperator A K negative i t x) =
      rootOperator A K negative i (σ t) (semilinearEquiv A K σ x) := by
  simp only [rootOperator, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    map_smulₛₗ, map_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [semilinearEquiv_integralOperator]
  rfl

def ambientAutomorphism : MulAut (Ambient A K) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Space A K)).symm.trans
    (LinearMap.GeneralLinearGroup.congrLinearEquiv (semilinearEquiv A K σ))).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Space A K))

theorem ambientAutomorphism_apply (g : Ambient A K) (x : Space A K) :
    ambientAutomorphism A K σ g x = semilinearEquiv A K σ
      (g ((semilinearEquiv A K σ).symm x)) := rfl

theorem ambientAutomorphism_isRootElement (negative : Bool) (i : Fin n) (t : K)
    (g : Ambient A K) (hg : IsRootElement A K negative i t g) :
    IsRootElement A K negative i (σ t) (ambientAutomorphism A K σ g) := by
  apply LinearMap.ext
  intro x
  change ambientAutomorphism A K σ g x = rootOperator A K negative i (σ t) x
  rw [ambientAutomorphism_apply]
  have hx := congrArg (fun f : Space A K →ₗ[K] Space A K =>
    f ((semilinearEquiv A K σ).symm x)) hg
  change g ((semilinearEquiv A K σ).symm x) = _ at hx
  rw [hx, semilinearEquiv_rootOperator, LinearEquiv.apply_symm_apply]

end SymmetricSubgroupAsymptotics.CFSGSerreField
