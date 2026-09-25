import SymmetricSubgroupAsymptotics.SchurMultiplicity
import SymmetricSubgroupAsymptotics.SchurRestriction

/-!
# Fractional Schur bounds for original group actions

The action on the source remains a representation of its actual acting
group. Only the target is inflated along a surjective quotient map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
universe u
variable {k D B V A : Type u} [Field k] [Group D] [Group B]
    [AddCommGroup V] [Module k V] [AddCommGroup A] [Module k A]

/-- Intrinsic Schur capacity of the actual target group representation. -/
def representationSchurCapacity (σ : Representation k B A) : ℝ :=
  schurCapacity k k[B] σ.asModule

/-- The finite-length estimate for the actual intertwining-map space. -/
theorem intertwiningMap_finrank_le_schur [FiniteDimensional k V] [FiniteDimensional k A]
    (ρ : Representation k B V) (σ : Representation k B A) :
    (Module.finrank k (ρ.IntertwiningMap σ) : ℝ) ≤
      representationSchurCapacity σ * Module.finrank k V := by
  rw [(Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).finrank_eq]
  simpa only [representationSchurCapacity, ← ρ.asModuleEquiv.finrank_eq] using
    (schurHom_finrank_le_capacity (k := k) (R := k[B])
      (A := σ.asModule) (M := ρ.asModule))

/-- Original target capacity is unchanged by a surjective group action map. -/
theorem representationSchurCapacity_comp [FiniteDimensional k A]
    (γ : D →* B) (hγ : Function.Surjective γ) (σ : Representation k B A) :
    representationSchurCapacity (σ.comp γ) = representationSchurCapacity σ := by
  letI : Module k[D] σ.asModule := Representation.instModuleMonoidAlgebraAsModule (σ.comp γ)
  letI : IsScalarTower k k[D] σ.asModule :=
    inferInstanceAs (IsScalarTower k k[D] (Representation.asModule (σ.comp γ)))
  have ha : ∀ r : k[D], ∀ a : σ.asModule,
      r • a = (MonoidAlgebra.mapDomainRingHom k γ) r • a := by
    intro r a
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, add_smul, add_smul, hx, hy]
    | single g t =>
      change (MonoidAlgebra.single g t) • (a : Representation.asModule (σ.comp γ)) = _
      rw [Representation.single_smul]
      simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
        Representation.single_smul]
      rfl
  exact schurCapacity_eq_of_surjective_action
    (k := k) (A := σ.asModule) (MonoidAlgebra.mapDomainRingHom k γ)
    (Finsupp.mapDomain_surjective hγ) ha

/-- Fractional Schur bound with the source action left on D and the
capacity computed over the original quotient B. -/
theorem intertwiningMap_finrank_le_original_schur
    [FiniteDimensional k V] [FiniteDimensional k A]
    (γ : D →* B) (hγ : Function.Surjective γ)
    (ρ : Representation k D V) (σ : Representation k B A) :
    (Module.finrank k (ρ.IntertwiningMap (σ.comp γ)) : ℝ) ≤
      representationSchurCapacity σ * Module.finrank k V := by
  simpa only [representationSchurCapacity_comp γ hγ σ] using
    intertwiningMap_finrank_le_schur ρ (σ.comp γ)

/-- The finite-field cardinal estimate for the same literal Hom space. -/
theorem intertwiningMap_card_le_original_schur
    [Finite k] [FiniteDimensional k V] [FiniteDimensional k A]
    (γ : D →* B) (hγ : Function.Surjective γ)
    (ρ : Representation k D V) (σ : Representation k B A) :
    (Nat.card (ρ.IntertwiningMap (σ.comp γ)) : ℝ) ≤
      (Nat.card k : ℝ) ^ (representationSchurCapacity σ * Module.finrank k V) := by
  haveI : FiniteDimensional k (ρ.IntertwiningMap (σ.comp γ)) :=
    Module.Finite.equiv
      (Representation.IntertwiningMap.equivLinearMapAsModule ρ (σ.comp γ)).symm
  rw [Module.natCard_eq_pow_finrank (K := k), Nat.cast_pow, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast Nat.card_pos (α := k)
  · exact intertwiningMap_finrank_le_original_schur γ hγ ρ σ

end SymmetricSubgroupAsymptotics
