import SymmetricSubgroupAsymptotics.SchurFiniteLength
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# The actual simple-socle Hom capacity

The capacity is defined from simple submodules of the actual target. Its
bound on arbitrary finite-dimensional sources is proved, not assumed.
It uses the original field and the original algebra action throughout.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

universe u
variable {k R A M N : Type u} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

/-- Precomposition transports actual module Hom spaces linearly over k,
even when the algebra R is noncommutative. -/
def schurHomCongrSource (e : M ≃ₗ[R] N) :
    (M →ₗ[R] A) ≃ₗ[k] (N →ₗ[R] A) where
  toFun f := f.comp e.symm.toLinearMap
  invFun f := f.comp e.toLinearMap
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Forgetting equivariance gives the elementary ambient Hom bound. -/
theorem schurHom_finrank_le_product [FiniteDimensional k M] [FiniteDimensional k A] :
    Module.finrank k (M →ₗ[R] A) ≤ Module.finrank k M * Module.finrank k A := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := LinearMap.restrictScalarsₗ k R M A k) (LinearMap.restrictScalars_injective k)
  simpa only [Module.finrank_linearMap] using h

/-- Exact Hom density of an actual simple submodule of the target. -/
def schurSimpleRatios (k R A : Type u) [Field k] [Ring R] [Algebra k R]
    [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A] : Set ℝ :=
  {x | ∃ S : Submodule R A, IsSimpleModule R S ∧
    x = (Module.finrank k (S →ₗ[R] A) : ℝ) / Module.finrank k S}

/-- The target's actual simple-socle capacity. Inserting zero handles
the zero module without assuming it has a simple constituent. -/
def schurCapacity (k R A : Type u) [Field k] [Ring R] [Algebra k R]
    [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A] : ℝ :=
  sSup (insert 0 (schurSimpleRatios k R A))

theorem schurSimpleRatio_le [FiniteDimensional k A]
    (S : Submodule R A) [IsSimpleModule R S] :
    (Module.finrank k (S →ₗ[R] A) : ℝ) / Module.finrank k S ≤ Module.finrank k A := by
  letI : FiniteDimensional k S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars k) S.subtype_injective
  haveI : Nontrivial S := IsSimpleModule.nontrivial R S
  have hp : (0 : ℝ) < Module.finrank k S := by exact_mod_cast (Module.finrank_pos (R := k) (M := S))
  apply (div_le_iff₀ hp).mpr
  simpa only [Nat.cast_mul, mul_comm] using
    (show (Module.finrank k (S →ₗ[R] A) : ℝ) ≤
      (Module.finrank k S * Module.finrank k A : ℕ) by exact_mod_cast
        (schurHom_finrank_le_product (k := k) (R := R) (M := S) (A := A)))

theorem schurCapacity_bddAbove [FiniteDimensional k A] :
    BddAbove (insert 0 (schurSimpleRatios k R A)) := by
  refine ⟨Module.finrank k A, ?_⟩
  rintro x (rfl | ⟨S,hS,rfl⟩)
  · positivity
  · letI := hS
    exact schurSimpleRatio_le S

theorem schurCapacity_nonneg [FiniteDimensional k A] : 0 ≤ schurCapacity k R A :=
  le_csSup schurCapacity_bddAbove (Set.mem_insert _ _)

theorem schurCapacity_le_dimension [FiniteDimensional k A] :
    schurCapacity k R A ≤ Module.finrank k A := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro x (rfl | ⟨S,hS,rfl⟩)
  · positivity
  · letI := hS
    exact schurSimpleRatio_le S

/-- Every simple-source Hom density is controlled by an actual simple
submodule of the target, or the entire Hom space is zero. -/
theorem schurHom_simple_le_capacity [FiniteDimensional k A]
    [FiniteDimensional k M] [IsSimpleModule R M] :
    (Module.finrank k (M →ₗ[R] A) : ℝ) ≤
      schurCapacity k R A * Module.finrank k M := by
  classical
  by_cases hz : ∀ f : M →ₗ[R] A, f = 0
  · haveI : Subsingleton (M →ₗ[R] A) := ⟨fun f g ↦ (hz f).trans (hz g).symm⟩
    rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
    exact mul_nonneg schurCapacity_nonneg (by positivity)
  · push Not at hz
    obtain ⟨f,hf⟩ := hz
    let e : M ≃ₗ[R] f.range := LinearEquiv.ofInjective f (LinearMap.injective_of_ne_zero hf)
    haveI : IsSimpleModule R f.range := IsSimpleModule.congr e.symm
    letI : FiniteDimensional k f.range := FiniteDimensional.of_injective
      (f.range.subtype.restrictScalars k) f.range.subtype_injective
    haveI : Nontrivial f.range := IsSimpleModule.nontrivial R f.range
    have hp : (0 : ℝ) < Module.finrank k f.range := by
      exact_mod_cast (Module.finrank_pos (R := k) (M := f.range))
    have hc : (Module.finrank k (f.range →ₗ[R] A) : ℝ) / Module.finrank k f.range ≤
        schurCapacity k R A :=
      le_csSup schurCapacity_bddAbove (Set.mem_insert_of_mem _ ⟨f.range,inferInstance,rfl⟩)
    rw [(schurHomCongrSource (k := k) (A := A) e).finrank_eq,
      (e.restrictScalars k).finrank_eq]
    exact (div_le_iff₀ hp).mp hc

/-- Closed finite-length Schur capacity bound for every actual source.
There is no local Hom estimate, semisimplicity, or algebraic-closure
hypothesis in this endpoint. -/
theorem schurHom_finrank_le_capacity [FiniteDimensional k A] [FiniteDimensional k M] :
    (Module.finrank k (M →ₗ[R] A) : ℝ) ≤
      schurCapacity k R A * Module.finrank k M := by
  apply schurHom_finiteDimensional_bound (schurCapacity k R A) (M := M)
  intro X _ _ _ _ _ _
  exact schurHom_simple_le_capacity

end SymmetricSubgroupAsymptotics
