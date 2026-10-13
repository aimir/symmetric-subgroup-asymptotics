import SymmetricSubgroupAsymptotics.SchurMultiplicity
import Mathlib.RepresentationTheory.Intertwining

/-!
# Schur multiplicity under a target-module equivalence

The Schur multiplicity is intrinsic to the target module.  This narrow
bridge lets downstream representation code cross between two explicit
module structures only after supplying an actual linear equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

universe u

variable {k R A V X : Type u} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]
  [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
  [AddCommGroup X] [Module R X] [Module k X] [IsScalarTower k R X]

/-- An explicit `R`-linear equivalence of finite-dimensional target
modules preserves the multiplicity of every simple source. -/
theorem schurSocleMultiplicity_eq_of_target_linearEquiv
    [FiniteDimensional k A] [FiniteDimensional k V]
    [FiniteDimensional k X] [IsSimpleModule R X]
    (e : A ≃ₗ[R] V) :
    schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X) =
      schurSocleMultiplicity (k := k) (R := R) (A := V) (X := X) := by
  letI : Nontrivial X := IsSimpleModule.nontrivial R X
  have hhom := (schurHomCongrTarget (k := k) (X := X) e).finrank_eq
  rw [schurHom_finrank_eq_multiplicity
        (k := k) (R := R) (A := A) (X := X),
    schurHom_finrank_eq_multiplicity
        (k := k) (R := R) (A := V) (X := X)] at hhom
  apply Nat.eq_of_mul_eq_mul_right
    (Module.finrank_pos (R := k) (M := Module.End R X))
  exact hhom

/-- An explicit equivalence of simple source modules preserves their Schur
multiplicity in every finite target. -/
theorem schurSocleMultiplicity_eq_of_source_linearEquiv
    {V : Type u} [AddCommGroup V] [Module R V] [Module k V]
    [IsScalarTower k R V]
    [FiniteDimensional k A] [FiniteDimensional k X]
    [FiniteDimensional k V]
    [IsSimpleModule R X] [IsSimpleModule R V]
    (e : X ≃ₗ[R] V) :
    schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X) =
      schurSocleMultiplicity (k := k) (R := R) (A := A) (X := V) := by
  letI : Nontrivial V := IsSimpleModule.nontrivial R V
  have hhom := (schurHomCongrSource (k := k) (A := A) e).finrank_eq
  have hend₁ := (schurHomCongrSource (k := k) (A := X) e).finrank_eq
  have hend₂ := (schurHomCongrTarget (k := k) (X := V) e).finrank_eq
  have hend : Module.finrank k (Module.End R X) =
      Module.finrank k (Module.End R V) := hend₁.trans hend₂
  rw [schurHom_finrank_eq_multiplicity
        (k := k) (R := R) (A := A) (X := X),
    schurHom_finrank_eq_multiplicity
        (k := k) (R := R) (A := A) (X := V), hend] at hhom
  apply Nat.eq_of_mul_eq_mul_right
    (Module.finrank_pos (R := k) (M := Module.End R V))
  exact hhom

/-- Equivalent finite modules have endomorphism rings of the same ground
field dimension. -/
theorem moduleEnd_finrank_eq_of_linearEquiv
    {V : Type u} [AddCommGroup V] [Module R V] [Module k V]
    [IsScalarTower k R V]
    [FiniteDimensional k X] [FiniteDimensional k V]
    (e : X ≃ₗ[R] V) :
    Module.finrank k (Module.End R X) =
      Module.finrank k (Module.End R V) := by
  exact (schurHomCongrSource (k := k) (A := X) e).finrank_eq.trans
    (schurHomCongrTarget (k := k) (X := V) e).finrank_eq

/-- Equivalent simple modules have the same dimension over their Schur
endomorphism division rings. -/
theorem moduleFinrankOverEnd_eq_of_linearEquiv
    {V : Type u} [AddCommGroup V] [Module R V] [Module k V]
    [IsScalarTower k R V]
    [FiniteDimensional k X] [FiniteDimensional k V]
    [IsSimpleModule R X] [IsSimpleModule R V]
    (e : X ≃ₗ[R] V) :
    Module.finrank (Module.End R X) X =
      Module.finrank (Module.End R V) V := by
  letI : Nontrivial V := IsSimpleModule.nontrivial R V
  have hdim := (e.restrictScalars k).finrank_eq
  have hend := moduleEnd_finrank_eq_of_linearEquiv (k := k) e
  have hX := schur_simple_finrank_tower (k := k) (R := R) (X := X)
  have hV := schur_simple_finrank_tower (k := k) (R := R) (X := V)
  rw [hX, hV, hend] at hdim
  apply Nat.eq_of_mul_eq_mul_left
    (Module.finrank_pos (R := k) (M := Module.End R V))
  exact hdim

/-- A representation equivalence is, in particular, an equivalence of the
corresponding group-algebra modules. -/
noncomputable def representationEquivLinearEquivAsModule
    {G B C : Type u} [Group G]
    [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C]
    (rho : Representation k G B) (sigma : Representation k G C)
    (e : rho.Equiv sigma) : rho.asModule ≃ₗ[k[G]] sigma.asModule where
  toLinearMap :=
    Representation.IntertwiningMap.equivLinearMapAsModule
      rho sigma e.toIntertwiningMap
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply

/-- Representation-equivalent finite targets have equal multiplicity in
every simple row. -/
theorem schurSocleMultiplicity_eq_of_representationEquiv
    {G B C : Type u} [Group G]
    [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C]
    [FiniteDimensional k B] [FiniteDimensional k C]
    [Module k[G] X] [IsScalarTower k k[G] X]
    [FiniteDimensional k X] [IsSimpleModule k[G] X]
    (rho : Representation k G B) (sigma : Representation k G C)
    (e : rho.Equiv sigma) :
    schurSocleMultiplicity
        (k := k) (R := k[G]) (A := rho.asModule) (X := X) =
      schurSocleMultiplicity
        (k := k) (R := k[G]) (A := sigma.asModule) (X := X) :=
  schurSocleMultiplicity_eq_of_target_linearEquiv
    (representationEquivLinearEquivAsModule rho sigma e)

end SymmetricSubgroupAsymptotics

end
