import SymmetricSubgroupAsymptotics.SchurMultiplicity
import SymmetricSubgroupAsymptotics.SchurRestriction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finiteness
import Mathlib.RepresentationTheory.Intertwining

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

/-- The group-algebra action of an inflated representation is restriction
along the map of group algebras induced by the acting group homomorphism. -/
theorem representation_comp_monoidAlgebra_smul
    (γ : D →* B) (σ : Representation k B A)
    (r : k[D]) (a : A) :
    r • (a : (σ.comp γ).asModule) =
      (MonoidAlgebra.mapDomainRingHom k γ) r • (a : σ.asModule) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, add_smul, add_smul, hx, hy]
  | single g t =>
      rw [Representation.single_smul]
      simp only [MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, Representation.single_smul]
      rfl

/-- A quotient-group submodule regarded as a submodule for a surjectively
inflated group action. -/
noncomputable def representationInflatedSubmodule
    (γ : D →* B) (hγ : Function.Surjective γ)
    (σ : Representation k B A)
    (S : Submodule k[B] σ.asModule) :
    Submodule k[D] (σ.comp γ).asModule :=
  (schurSubmoduleOrderIso
    (MonoidAlgebra.mapDomainRingHom k γ)
    (Finsupp.mapDomain_surjective hγ)
    (representation_comp_monoidAlgebra_smul γ σ)).symm S

theorem representationInflatedSubmodule_isSimple
    (γ : D →* B) (hγ : Function.Surjective γ)
    (σ : Representation k B A)
    (S : Submodule k[B] σ.asModule) [IsSimpleModule k[B] S] :
    IsSimpleModule k[D] (representationInflatedSubmodule γ hγ σ S) := by
  let e := schurSubmoduleOrderIso
    (MonoidAlgebra.mapDomainRingHom k γ)
    (Finsupp.mapDomain_surjective hγ)
    (representation_comp_monoidAlgebra_smul γ σ)
  rw [isSimpleModule_iff_isAtom]
  exact (e.isAtom_iff (representationInflatedSubmodule γ hγ σ S)).mp
    (by
      simpa only [representationInflatedSubmodule, e,
        OrderIso.apply_symm_apply] using
        (isSimpleModule_iff_isAtom.mp
          (inferInstance : IsSimpleModule k[B] S)))

/-- Schur multiplicity is unchanged when both target and simple row are
inflated along a surjective acting-group map. -/
theorem schurSocleMultiplicity_comp_eq
    [FiniteDimensional k A]
    (γ : D →* B) (hγ : Function.Surjective γ)
    (σ : Representation k B A)
    (S : Submodule k[B] σ.asModule)
    [FiniteDimensional k S] [IsSimpleModule k[B] S] :
    schurSocleMultiplicity
        (k := k) (R := k[D]) (A := (σ.comp γ).asModule)
        (X := representationInflatedSubmodule γ hγ σ S) =
      schurSocleMultiplicity
        (k := k) (R := k[B]) (A := σ.asModule) (X := S) := by
  let φ := MonoidAlgebra.mapDomainRingHom k γ
  let hφ : Function.Surjective φ := Finsupp.mapDomain_surjective hγ
  let ha := representation_comp_monoidAlgebra_smul γ σ
  let S' := representationInflatedSubmodule γ hγ σ S
  letI : IsSimpleModule k[D] S' :=
    representationInflatedSubmodule_isSimple γ hγ σ S
  have h := schurSocleMultiplicity_eq_of_surjective_action
    φ hφ ha S'
  simpa only [S', representationInflatedSubmodule, φ, hφ, ha,
    OrderIso.apply_symm_apply] using h

/-- The intrinsic Schur capacity of a representation is never larger than
the dimension of its underlying target space. -/
theorem representationSchurCapacity_le_dimension [FiniteDimensional k A]
    (σ : Representation k B A) :
    representationSchurCapacity σ ≤ Module.finrank k A := by
  unfold representationSchurCapacity
  letI : Module k[B] σ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule σ
  letI : IsScalarTower k k[B] σ.asModule :=
    inferInstanceAs (IsScalarTower k k[B] (Representation.asModule σ))
  calc
    schurCapacity k k[B] σ.asModule ≤
        Module.finrank k σ.asModule := schurCapacity_le_dimension
    _ = Module.finrank k A := by
      exact_mod_cast σ.asModuleEquiv.finrank_eq

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
  exact schurCapacity_eq_of_surjective_action
    (k := k) (A := σ.asModule) (MonoidAlgebra.mapDomainRingHom k γ)
    (Finsupp.mapDomain_surjective hγ)
    (representation_comp_monoidAlgebra_smul γ σ)

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
