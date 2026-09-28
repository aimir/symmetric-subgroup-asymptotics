import SymmetricSubgroupAsymptotics.SchurRepresentation
import Mathlib.RepresentationTheory.Invariants

/-!
# Trivial and nontrivial rows of representation Schur capacity

The intrinsic Schur capacity is a supremum over actual simple submodules.
This file separates that supremum into the fixed simple row and a supplied
bound for every nonfixed simple row.  The fixed row is bounded by the
dimension of the literal invariant subspace.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

universe u
variable {k B A : Type u} [Field k] [Group B]
    [AddCommGroup A] [Module k A]

/-- An actual simple submodule is in the trivial row when every original
group element fixes all of its vectors. -/
def representationSubmoduleFixed
    (σ : Representation k B A) (S : Submodule k[B] σ.asModule) : Prop :=
  ∀ (g : B) (x : S), MonoidAlgebra.single g (1 : k) • x = x

/-- Forget equivariance while retaining the proof that the image lies in
the original invariant subspace. -/
def simpleHomToInvariantsOfFixed
    (σ : Representation k B A) (S : Submodule k[B] σ.asModule)
    (hfixed : representationSubmoduleFixed σ S) :
    (S →ₗ[k[B]] σ.asModule) →ₗ[k] (S →ₗ[k] σ.invariants) where
  toFun f := (σ.asModuleEquiv.toLinearMap.comp (f.restrictScalars k)).codRestrict
    σ.invariants (fun x g => by
      have h := f.map_smul (MonoidAlgebra.single g (1 : k)) x
      rw [hfixed g x] at h
      simpa only [Representation.single_smul, one_smul] using h.symm)
  map_add' f g := by ext x; rfl
  map_smul' t f := by ext x; rfl

theorem simpleHomToInvariantsOfFixed_injective
    (σ : Representation k B A) (S : Submodule k[B] σ.asModule)
    (hfixed : representationSubmoduleFixed σ S) :
    Function.Injective (simpleHomToInvariantsOfFixed σ S hfixed) := by
  intro f g h
  apply LinearMap.ext
  intro x
  apply σ.asModuleEquiv.injective
  exact congrArg Subtype.val
    (congrArg (fun F : S →ₗ[k] σ.invariants => F x) h)

/-- Every fixed simple row has density at most the dimension of the
literal invariant subspace of the target. -/
theorem schurSimpleRatio_le_invariants_of_fixed
    [FiniteDimensional k A]
    (σ : Representation k B A) (S : Submodule k[B] σ.asModule)
    [IsSimpleModule k[B] S]
    (hfixed : representationSubmoduleFixed σ S) :
    (Module.finrank k (S →ₗ[k[B]] σ.asModule) : ℝ) /
        Module.finrank k S ≤ Module.finrank k σ.invariants := by
  letI : FiniteDimensional k S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars k) S.subtype_injective
  haveI : Nontrivial S := IsSimpleModule.nontrivial k[B] S
  have hdim : 0 < (Module.finrank k S : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := k) (M := S))
  have h := LinearMap.finrank_le_finrank_of_injective
    (simpleHomToInvariantsOfFixed_injective σ S hfixed)
  rw [Module.finrank_linearMap k k S σ.invariants] at h
  apply (div_le_iff₀ hdim).mpr
  have hR :
      (Module.finrank k (S →ₗ[k[B]] σ.asModule) : ℝ) ≤
        (Module.finrank k S : ℝ) * Module.finrank k σ.invariants := by
    exact_mod_cast h
  simpa only [mul_comm] using hR

/-- Bounding every nonfixed simple row by `r` bounds the whole intrinsic
Schur capacity by the maximum of the actual fixed row and `r`. -/
theorem representationSchurCapacity_le_max_fixed_nontrivial
    [FiniteDimensional k A]
    (σ : Representation k B A) (r : ℝ)
    (hnontrivial : ∀ (S : Submodule k[B] σ.asModule),
      IsSimpleModule k[B] S →
      ¬ representationSubmoduleFixed σ S →
      (Module.finrank k (S →ₗ[k[B]] σ.asModule) : ℝ) /
          Module.finrank k S ≤ r) :
    representationSchurCapacity σ ≤
      max (Module.finrank k σ.invariants : ℝ) r := by
  unfold representationSchurCapacity schurCapacity
  apply csSup_le (Set.insert_nonempty _ _)
  rintro x (rfl | ⟨S, hS, rfl⟩)
  · exact (by positivity : (0 : ℝ) ≤ Module.finrank k σ.invariants).trans
      (le_max_left _ _)
  · letI := hS
    by_cases hfixed : representationSubmoduleFixed σ S
    · exact (schurSimpleRatio_le_invariants_of_fixed σ S hfixed).trans
        (le_max_left _ _)
    · exact (hnontrivial S hS hfixed).trans (le_max_right _ _)

/-- The actual nonfixed simple-socle densities of a representation. -/
def representationNonfixedSchurRatios
    (σ : Representation k B A) : Set ℝ :=
  {x | ∃ S : Submodule k[B] σ.asModule,
    IsSimpleModule k[B] S ∧
    ¬ representationSubmoduleFixed σ S ∧
    x = (Module.finrank k (S →ₗ[k[B]] σ.asModule) : ℝ) /
      Module.finrank k S}

/-- The concrete nontrivial row in the manuscript's coupled estimate. -/
def representationNonfixedSchurCapacity
    (σ : Representation k B A) : ℝ :=
  sSup (insert 0 (representationNonfixedSchurRatios σ))

theorem representationNonfixedSchurCapacity_bddAbove
    [FiniteDimensional k A] (σ : Representation k B A) :
    BddAbove (insert 0 (representationNonfixedSchurRatios σ)) := by
  refine ⟨Module.finrank k A, ?_⟩
  rintro x (rfl | ⟨S, hS, _, rfl⟩)
  · positivity
  · letI := hS
    exact schurSimpleRatio_le S

theorem representationNonfixedSchurCapacity_nonneg
    [FiniteDimensional k A] (σ : Representation k B A) :
    0 ≤ representationNonfixedSchurCapacity σ :=
  le_csSup (representationNonfixedSchurCapacity_bddAbove σ)
    (Set.mem_insert _ _)

theorem schurSimpleRatio_le_nonfixedCapacity
    [FiniteDimensional k A]
    (σ : Representation k B A) (S : Submodule k[B] σ.asModule)
    [IsSimpleModule k[B] S]
    (hfixed : ¬ representationSubmoduleFixed σ S) :
    (Module.finrank k (S →ₗ[k[B]] σ.asModule) : ℝ) /
        Module.finrank k S ≤ representationNonfixedSchurCapacity σ :=
  le_csSup (representationNonfixedSchurCapacity_bddAbove σ)
    (Set.mem_insert_of_mem _ ⟨S, inferInstance, hfixed, rfl⟩)

/-- The intrinsic capacity is exactly reduced to its literal fixed row and
the concrete supremum over nonfixed simple rows. -/
theorem representationSchurCapacity_le_max_fixed_nonfixed
    [FiniteDimensional k A] (σ : Representation k B A) :
    representationSchurCapacity σ ≤
      max (Module.finrank k σ.invariants : ℝ)
        (representationNonfixedSchurCapacity σ) := by
  apply representationSchurCapacity_le_max_fixed_nontrivial σ
  intro S hS hfixed
  letI := hS
  exact schurSimpleRatio_le_nonfixedCapacity σ S hfixed

end SymmetricSubgroupAsymptotics

end
