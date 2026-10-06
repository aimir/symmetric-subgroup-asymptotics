import SymmetricSubgroupAsymptotics.SchurMultiplicity

/-!
# Schur multiplicity under a target-module equivalence

The Schur multiplicity is intrinsic to the target module.  This narrow
bridge lets downstream representation code cross between two explicit
module structures only after supplying an actual linear equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k R A V X : Type} [Field k] [Ring R] [Algebra k R]
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

end SymmetricSubgroupAsymptotics

end
