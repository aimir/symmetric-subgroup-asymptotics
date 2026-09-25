import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.FiniteLength

/-!
# Finite-length Hom estimates over the original coefficient field

Restriction and quotient descent are carried out for actual module maps.
The source need not be semisimple, and the field need not be algebraically
closed. The resulting induction applies to the actual normalizer action.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

universe u
section Restriction
variable {k R M A : Type u} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]

/-- Restriction to one actual submodule, as a linear map on Hom spaces. -/
def schurHomRestriction (S : Submodule R M) :
    (M →ₗ[R] A) →ₗ[k] (S →ₗ[R] A) where
  toFun f := f.comp S.subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Maps vanishing on S are exactly maps from the actual quotient M/S.
The equivalence is linear over the original field. -/
def schurHomRestrictionKernelEquiv (S : Submodule R M) :
    LinearMap.ker (schurHomRestriction (k := k) (A := A) S) ≃ₗ[k]
      ((M ⧸ S) →ₗ[R] A) where
  toFun f := S.liftQ f.1 (by
    intro x hx
    exact DFunLike.congr_fun f.2 (⟨x,hx⟩ : S))
  invFun f := ⟨f.comp S.mkQ, by
    ext x
    change f (S.mkQ x) = 0
    have hx : S.mkQ (x : M) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr x.property
    rw [hx, map_zero]⟩
  left_inv f := by
    apply Subtype.ext
    ext x
    rfl
  right_inv f := by
    ext x
    rfl
  map_add' _ _ := by
    ext x
    rfl
  map_smul' _ _ := by
    ext x
    rfl

/-- Left exactness of Hom gives the dimension inequality needed for
finite-length induction. No extension of maps from S is assumed. -/
theorem schurHom_finrank_le_submodule_quotient
    [FiniteDimensional k M] [FiniteDimensional k A] (S : Submodule R M) :
    Module.finrank k (M →ₗ[R] A) ≤
      Module.finrank k (S →ₗ[R] A) + Module.finrank k ((M ⧸ S) →ₗ[R] A) := by
  letI : FiniteDimensional k S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars k) S.subtype_injective
  letI : FiniteDimensional k (M ⧸ S) := FiniteDimensional.of_surjective
    (S.mkQ.restrictScalars k) S.mkQ_surjective
  have h := LinearMap.finrank_range_add_finrank_ker (schurHomRestriction (k := k) (A := A) S)
  rw [(schurHomRestrictionKernelEquiv (k := k) (A := A) S).finrank_eq] at h
  have hr := Submodule.finrank_le
    (LinearMap.range (schurHomRestriction (k := k) (A := A) S))
  omega

end Restriction

section Induction

variable {k R A : Type u} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]
    [FiniteDimensional k A]

/-- A simple-source Hom bound propagates through every finite extension.
This is an actual finite-length induction, with no semisimplicity premise. -/
theorem schurHom_finiteLength_bound (c : ℝ)
    (hsimple : ∀ (X : Type u) [AddCommGroup X] [Module R X] [Module k X]
      [IsScalarTower k R X] [FiniteDimensional k X] [IsSimpleModule R X],
      (Module.finrank k (X →ₗ[R] A) : ℝ) ≤ c * Module.finrank k X)
    {M : Type u} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    ∀ [Module k M] [IsScalarTower k R M] [FiniteDimensional k M],
      (Module.finrank k (M →ₗ[R] A) : ℝ) ≤ c * Module.finrank k M := by
  induction hM with
  | of_subsingleton =>
    intro _ _ _
    simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero, le_refl]
  | @of_simple_quotient M _ _ S hsimpleS hlength ih =>
    intro _ _ _
    letI : FiniteDimensional k S := FiniteDimensional.of_injective
      (S.subtype.restrictScalars k) S.subtype_injective
    letI : FiniteDimensional k (M ⧸ S) := FiniteDimensional.of_surjective
      (S.mkQ.restrictScalars k) S.mkQ_surjective
    have h₁ := ih
    have h₂ := hsimple (M ⧸ S)
    have h₃ := schurHom_finrank_le_submodule_quotient (k := k) (A := A) S
    have hd : Module.finrank k (M ⧸ S) + Module.finrank k S = Module.finrank k M :=
      (S.restrictScalars k).finrank_quotient_add_finrank
    have h₃' : (Module.finrank k (M →ₗ[R] A) : ℝ) ≤
        Module.finrank k (S →ₗ[R] A) + Module.finrank k ((M ⧸ S) →ₗ[R] A) :=
      by exact_mod_cast h₃
    have hd' : (Module.finrank k (M ⧸ S) : ℝ) + Module.finrank k S = Module.finrank k M :=
      by exact_mod_cast hd
    calc
      _ ≤ _ := h₃'
      _ ≤ c * Module.finrank k S + c * Module.finrank k (M ⧸ S) := add_le_add h₁ h₂
      _ = _ := by rw [← mul_add, add_comm, hd']

/-- Finite-dimensional sources have finite length for any original
algebra action, so the preceding induction is unconditional on the source. -/
theorem schurHom_finiteDimensional_bound (c : ℝ)
    (hsimple : ∀ (X : Type u) [AddCommGroup X] [Module R X] [Module k X]
      [IsScalarTower k R X] [FiniteDimensional k X] [IsSimpleModule R X],
      (Module.finrank k (X →ₗ[R] A) : ℝ) ≤ c * Module.finrank k X)
    (M : Type u) [AddCommGroup M] [Module R M] [Module k M]
    [IsScalarTower k R M] [FiniteDimensional k M] :
    (Module.finrank k (M →ₗ[R] A) : ℝ) ≤ c * Module.finrank k M := by
  apply schurHom_finiteLength_bound c hsimple
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

end Induction

end SymmetricSubgroupAsymptotics
