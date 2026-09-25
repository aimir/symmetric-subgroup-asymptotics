import SymmetricSubgroupAsymptotics.SchurCapacity
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Actual socle multiplicities over Schur division rings

Every map from a simple module lands in its actual isotypic component
inside the target. This identifies the intrinsic Hom density with the
socle multiplicity divided by the simple dimension over its Schur ring.
The source and the entire target need not be semisimple.
-/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
universe u
variable {k R A X Y : Type u} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]
    [AddCommGroup X] [Module R X] [Module k X] [IsScalarTower k R X]
    [AddCommGroup Y] [Module R Y] [Module k Y] [IsScalarTower k R Y]

/-- Postcomposition preserves the original algebra action. -/
def schurHomCongrTarget (e : A ≃ₗ[R] Y) :
    (X →ₗ[R] A) ≃ₗ[k] (X →ₗ[R] Y) where
  toFun f := e.toLinearMap.comp f
  invFun f := e.symm.toLinearMap.comp f
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; exact e.map_add _ _
  map_smul' c f := by ext x; exact (e.restrictScalars k).map_smul c (f x)

/-- A simple-source map has image in the literal isotypic component. -/
theorem schurHom_range_le_isotypic [IsSimpleModule R X] (f : X →ₗ[R] A) :
    f.range ≤ isotypicComponent R A X := by
  classical
  by_cases hf : f = 0
  · subst f; simp
  · exact le_sSup ⟨(LinearEquiv.ofInjective f
      (LinearMap.injective_of_ne_zero hf)).symm⟩

/-- Restrict the codomain to the actual socle component; no maps are lost. -/
def schurHomIsotypicEquiv [IsSimpleModule R X] :
    (X →ₗ[R] A) ≃ₗ[k] (X →ₗ[R] isotypicComponent R A X) where
  toFun f := f.codRestrict _ fun x ↦ schurHom_range_le_isotypic f ⟨x, rfl⟩
  invFun f := (isotypicComponent R A X).subtype.comp f
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

/-- Coordinate evaluation is the genuine Hom-to-product equivalence. -/
def schurHomFinEquiv (n : ℕ) :
    (X →ₗ[R] (Fin n → X)) ≃ₗ[k] (Fin n → Module.End R X) where
  toFun f i := (LinearMap.proj i).comp f
  invFun f := LinearMap.pi f
  left_inv f := by ext x i; rfl
  right_inv f := by ext i x; rfl
  map_add' f g := by ext i x; rfl
  map_smul' c f := by ext i x; rfl

omit [Module k X] [IsScalarTower k R X] in
/-- Actual finite socle decomposition, obtained from submodules inside A. -/
theorem schurIsotypic_exists_equiv [FiniteDimensional k A] [IsSimpleModule R X] :
    ∃ n : ℕ, Nonempty (isotypicComponent R A X ≃ₗ[R] (Fin n → X)) := by
  let C := isotypicComponent R A X
  letI : FiniteDimensional k C := FiniteDimensional.of_injective
    (C.subtype.restrictScalars k) C.subtype_injective
  letI : Module.Finite R C := Module.Finite.of_restrictScalars_finite k R C
  exact (IsIsotypicOfType.isotypicComponent R A X).linearEquiv_fun

/-- The actual multiplicity counts copies in the simple socle component. -/
def schurSocleMultiplicity [FiniteDimensional k A] [IsSimpleModule R X] : ℕ :=
  (schurIsotypic_exists_equiv (k := k) (R := R) (A := A) (X := X)).choose

def schurSocleDecomposition [FiniteDimensional k A] [IsSimpleModule R X] :
    isotypicComponent R A X ≃ₗ[R]
      (Fin (schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X)) → X) :=
  (schurIsotypic_exists_equiv (k := k) (R := R) (A := A) (X := X)).choose_spec.some

/-- The Hom-space dimension is the socle multiplicity times the actual
Schur division-ring dimension over the original field. -/
theorem schurHom_finrank_eq_multiplicity [FiniteDimensional k A]
    [FiniteDimensional k X] [IsSimpleModule R X] :
    Module.finrank k (X →ₗ[R] A) =
      schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X) *
        Module.finrank k (Module.End R X) := by
  let e := (schurHomIsotypicEquiv (k := k) (R := R) (A := A) (X := X)).trans
    ((schurHomCongrTarget (k := k) (X := X) (schurSocleDecomposition
      (k := k) (R := R) (A := A) (X := X))).trans (schurHomFinEquiv (k := k) _))
  simpa [Module.finrank_pi_fintype] using e.finrank_eq

/-- Schur's division ring acts on the original simple module; the tower
law is valid without assuming that division ring is the base field. -/
theorem schur_simple_finrank_tower [FiniteDimensional k X] [IsSimpleModule R X] :
    Module.finrank k X = Module.finrank k (Module.End R X) *
      Module.finrank (Module.End R X) X := by
  classical
  exact (Module.finrank_mul_finrank k (Module.End R X) X).symm

/-- The manuscript's fractional Schur ratio equals the intrinsic
simple-source Hom density, with an actual socle multiplicity. -/
theorem schurSimpleRatio_eq_multiplicity_division [FiniteDimensional k A]
    [FiniteDimensional k X] [IsSimpleModule R X] :
    (Module.finrank k (X →ₗ[R] A) : ℝ) / Module.finrank k X =
      (schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X) : ℝ) /
        Module.finrank (Module.End R X) X := by
  classical
  haveI : Nontrivial X := IsSimpleModule.nontrivial R X
  have hE : (Module.finrank k (Module.End R X) : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := k) (M := Module.End R X)).ne'
  rw [schurHom_finrank_eq_multiplicity, schur_simple_finrank_tower (k := k) (R := R) (X := X),
    Nat.cast_mul, Nat.cast_mul]
  field_simp

end SymmetricSubgroupAsymptotics
