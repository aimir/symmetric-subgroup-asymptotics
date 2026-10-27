import SymmetricSubgroupAsymptotics.FiniteIntegralFamilyScaledRetraction
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! An actual integral retraction up to d can be established from a
RATIONAL source spanning theorem. The coordinate map remains integer
valued on the literal integral source; hence its reconstructed vector
is integral and equals d times the original vector. No integral span,
saturation, target-lattice restriction, or flatness is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
namespace SymmetricSubgroupAsymptotics.FiniteIntegralRationalFamilyScaledRetraction
variable {J L N : Type*} [Fintype J] [DecidableEq J]
  [AddCommGroup L] [Module ℚ L] (S : Submodule ℤ L)
  [AddCommGroup N] [Module ℤ N]
  (f : S →ₗ[ℤ] N) (v : J → S) (c : N →ₗ[ℤ] (J → ℤ))
  (C : L →ₗ[ℚ] (J → ℚ)) (d : ℤ)

theorem reconstruction_of_rational_mem
    (hcoord : ∀ j, C (v j).val = (d : ℚ) • Pi.single j 1)
    (hcast : ∀ x : S, C x.val = fun j => (c (f x) j : ℚ))
    (x : S) (hx : x.val ∈ Submodule.span ℚ (Set.range (fun j => (v j).val))) :
    Fintype.linearCombination ℤ v (c (f x)) = d • x := by
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  have hc : C (Fintype.linearCombination ℚ (fun j => (v j).val) b) = (d : ℚ) • b := by
    rw [Fintype.linearCombination_apply]
    simp only [map_sum, map_smulₛₗ, RingHom.id_apply, hcoord]
    funext j
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [Fintype.linearCombination_apply, hb, hcast] at hc
  have hcoeff (j : J) : (c (f x) j : ℚ) = (d : ℚ) * b j := congrFun hc j
  apply Subtype.ext
  change (Fintype.linearCombination ℤ v (c (f x))).val = d • x.val
  rw [Fintype.linearCombination_apply, Submodule.coe_sum]
  rw [← hb, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Submodule.coe_smul]
  calc
    (c (f x) j : ℤ) • (v j).val = (c (f x) j : ℚ) • (v j).val :=
      (Int.cast_smul_eq_zsmul ℚ _ _).symm
    _ = ((d : ℚ) * b j) • (v j).val := by rw [hcoeff]
    _ = d • (b j • (v j).val) := by rw [mul_smul, Int.cast_smul_eq_zsmul]

theorem retraction_comp_of_rational_span
    (hcoord : ∀ j, C (v j).val = (d : ℚ) • Pi.single j 1)
    (hcast : ∀ x : S, C x.val = fun j => (c (f x) j : ℚ))
    (hspan : Submodule.span ℚ (Set.range (fun j => (v j).val)) = ⊤) :
    (FiniteIntegralFamilyScaledRetraction.retraction v c).comp f = d • LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact reconstruction_of_rational_mem S f v c C d hcoord hcast x (by rw [hspan]; trivial)

theorem baseChange_injective_of_rational_span
    (hcoord : ∀ j, C (v j).val = (d : ℚ) • Pi.single j 1)
    (hcast : ∀ x : S, C x.val = fun j => (c (f x) j : ℚ))
    (hspan : Submodule.span ℚ (Set.range (fun j => (v j).val)) = ⊤)
    (K : Type*) [Field K] (hd : (d : K) ≠ 0) : Function.Injective (f.baseChange K) := by
  let g := FiniteIntegralFamilyScaledRetraction.retraction v c
  have hgf : g.comp f = d • LinearMap.id :=
    retraction_comp_of_rational_span S f v c C d hcoord hcast hspan
  have h := congrArg (fun F : S →ₗ[ℤ] S => F.baseChange K) hgf
  change (g.comp f).baseChange K =
    (d • (LinearMap.id : S →ₗ[ℤ] S)).baseChange K at h
  let bc : (S →ₗ[ℤ] S) →+ (K ⊗[ℤ] S →ₗ[K] K ⊗[ℤ] S) :=
    { toFun := fun F => F.baseChange K
      map_zero' := by exact LinearMap.baseChange_zero
      map_add' := fun F G => LinearMap.baseChange_add F G }
  have hs := bc.map_zsmul d (LinearMap.id : S →ₗ[ℤ] S)
  change (d • (LinearMap.id : S →ₗ[ℤ] S)).baseChange K =
    d • (LinearMap.id : S →ₗ[ℤ] S).baseChange K at hs
  rw [LinearMap.baseChange_id] at hs
  rw [LinearMap.baseChange_comp, hs] at h
  have hleft : Function.LeftInverse (fun y => (d : K)⁻¹ • g.baseChange K y) (f.baseChange K) := by
    intro x
    change (d : K)⁻¹ • g.baseChange K (f.baseChange K x) = x
    have hx : g.baseChange K (f.baseChange K x) = d • x := LinearMap.congr_fun h x
    rw [hx, ← Int.cast_smul_eq_zsmul K]
    simp only [smul_smul, inv_mul_cancel₀ hd, one_smul]
  exact hleft.injective

end SymmetricSubgroupAsymptotics.FiniteIntegralRationalFamilyScaledRetraction
