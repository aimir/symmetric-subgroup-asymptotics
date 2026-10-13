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

/-- Composition with an acting-group homomorphism, with the representation
type retained explicitly so downstream module structures elaborate
without falling back to the underlying monoid homomorphism API. -/
abbrev inflatedRepresentation (γ : D →* B) (σ : Representation k B A) :
    Representation k D A :=
  σ.comp γ

/-- The group-algebra action attached to a representation, made explicit
to avoid asking typeclass search to recover the representation from the
bare underlying carrier. -/
def representationAlgebraSmul {H : Type u} [Group H]
    (ρ : Representation k H A) (r : k[H]) (a : A) : A := by
  letI : Module k[H] A :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  exact r • a

/-- The group-algebra action of an inflated representation is restriction
along the map of group algebras induced by the acting group homomorphism. -/
theorem representation_comp_monoidAlgebra_smul
    (γ : D →* B) (σ : Representation k B A)
    (r : k[D]) (a : A) :
    representationAlgebraSmul (inflatedRepresentation γ σ) r a =
      representationAlgebraSmul σ
        ((MonoidAlgebra.mapDomainRingHom k γ) r) a := by
  letI : Module k[D] A :=
    Representation.instModuleMonoidAlgebraAsModule
      (inflatedRepresentation γ σ)
  letI : Module k[B] A :=
    Representation.instModuleMonoidAlgebraAsModule σ
  change r • a = (MonoidAlgebra.mapDomainRingHom k γ) r • a
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, add_smul, add_smul, hx, hy]
  | single g t =>
      rw [Representation.single_smul]
      simp only [MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single]
      change t • σ (γ g) a = MonoidAlgebra.single (γ g) t • a
      rw [Representation.single_smul]
      rfl

/-- A quotient-group submodule regarded as a submodule for a surjectively
inflated group action. -/
noncomputable def representationInflatedSubmodule
    (γ : D →* B) (hγ : Function.Surjective γ)
    (σ : Representation k B A)
    (S : Submodule k[B] σ.asModule) :
    Submodule k[D] (inflatedRepresentation γ σ).asModule := by
  letI : Module k[D] A :=
    Representation.instModuleMonoidAlgebraAsModule
      (inflatedRepresentation γ σ)
  letI : Module k[B] A :=
    Representation.instModuleMonoidAlgebraAsModule σ
  let ha : ∀ r : k[D], ∀ a : A,
      r • a = (MonoidAlgebra.mapDomainRingHom k γ) r • a := by
    intro r a
    simpa only [representationAlgebraSmul] using
      representation_comp_monoidAlgebra_smul γ σ r a
  exact (schurSubmoduleOrderIso
    (MonoidAlgebra.mapDomainRingHom k γ)
    (Finsupp.mapDomain_surjective hγ) ha).symm S

theorem representationInflatedSubmodule_isSimple
    (γ : D →* B) (hγ : Function.Surjective γ)
    (σ : Representation k B A)
    (S : Submodule k[B] σ.asModule) [IsSimpleModule k[B] S] :
    IsSimpleModule k[D] (representationInflatedSubmodule γ hγ σ S) := by
  letI : Module k[D] A :=
    Representation.instModuleMonoidAlgebraAsModule
      (inflatedRepresentation γ σ)
  letI : Module k[B] A :=
    Representation.instModuleMonoidAlgebraAsModule σ
  let ha : ∀ r : k[D], ∀ a : A,
      r • a = (MonoidAlgebra.mapDomainRingHom k γ) r • a := by
    intro r a
    simpa only [representationAlgebraSmul] using
      representation_comp_monoidAlgebra_smul γ σ r a
  let e := schurSubmoduleOrderIso
    (MonoidAlgebra.mapDomainRingHom k γ)
    (Finsupp.mapDomain_surjective hγ)
    ha
  rw [isSimpleModule_iff_isAtom]
  exact (e.isAtom_iff (representationInflatedSubmodule γ hγ σ S)).mp
    (by
      simpa only [representationInflatedSubmodule, e,
        OrderIso.apply_symm_apply] using
        (isSimpleModule_iff_isAtom.mp
          (inferInstance : IsSimpleModule k[B] S)))

/-- The representation carried by an inflated submodule is the inflation of
the representation carried by the original quotient-group submodule. -/
noncomputable def representationInflatedSubmoduleEquiv
    (γ : D →* B) (hγ : Function.Surjective γ)
    (σ : Representation k B A)
    (S : Submodule k[B] σ.asModule) :
    Representation.Equiv
      (inflatedRepresentation γ
        (Subrepresentation.ofSubmodule' S).toRepresentation)
      (Subrepresentation.ofSubmodule'
        (representationInflatedSubmodule γ hγ σ S)).toRepresentation := by
  have hmem (a : A) :
      a ∈ representationInflatedSubmodule γ hγ σ S ↔ a ∈ S := by
    unfold representationInflatedSubmodule
    rfl
  let eLinear :
      (Subrepresentation.ofSubmodule' S).toSubmodule ≃ₗ[k]
        (Subrepresentation.ofSubmodule'
          (representationInflatedSubmodule γ hγ σ S)).toSubmodule := {
    toFun := fun x ↦ ⟨x.1, (hmem x.1).mpr x.2⟩
    invFun := fun x ↦ ⟨x.1, (hmem x.1).mp x.2⟩
    left_inv x := Subtype.ext rfl
    right_inv x := Subtype.ext rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  exact Representation.Equiv.mk eLinear (by
    intro d
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl)

/-- Intertwining maps are unchanged when both representations are inflated
along a surjective acting-group map. -/
noncomputable def representationIntertwiningCompEquiv
    (γ : D →* B) (hγ : Function.Surjective γ)
    (ρ : Representation k B V) (σ : Representation k B A) :
    ρ.IntertwiningMap σ ≃ₗ[k]
      (inflatedRepresentation γ ρ).IntertwiningMap
        (inflatedRepresentation γ σ) where
  toFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' d := f.isIntertwining' (γ d) }
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' := by
        intro b
        obtain ⟨d, rfl⟩ := hγ b
        exact f.isIntertwining' d }
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
  map_add' f g := by ext; rfl
  map_smul' c f := by ext; rfl

/-- Simplicity of a representation module is preserved by inflation along
a surjective acting-group map. -/
theorem representation_comp_isSimpleModule
    (γ : D →* B) (hγ : Function.Surjective γ)
    (ρ : Representation k B V) [IsSimpleModule k[B] ρ.asModule] :
    IsSimpleModule k[D] (inflatedRepresentation γ ρ).asModule := by
  let φ := MonoidAlgebra.mapDomainRingHom k γ
  letI : RingHomSurjective φ := ⟨Finsupp.mapDomain_surjective hγ⟩
  let f : (inflatedRepresentation γ ρ).asModule →ₛₗ[φ] ρ.asModule :=
    { toFun := fun x ↦ x
      map_add' := by intro x y; rfl
      map_smul' := by
        intro r x
        exact representation_comp_monoidAlgebra_smul γ ρ r x }
  exact (f.isSimpleModule_iff_of_bijective ⟨Function.injective_id,
    Function.surjective_id⟩).mpr inferInstance

/-- The Schur endomorphism dimension of a representation is unchanged by
surjective inflation. -/
theorem representationEnd_finrank_comp_eq
    [FiniteDimensional k V]
    (γ : D →* B) (hγ : Function.Surjective γ)
    (ρ : Representation k B V) :
    Module.finrank k
      (Module.End k[D] (inflatedRepresentation γ ρ).asModule) =
      Module.finrank k (Module.End k[B] ρ.asModule) := by
  rw [← (Representation.IntertwiningMap.equivLinearMapAsModule
    (inflatedRepresentation γ ρ)
      (inflatedRepresentation γ ρ)).finrank_eq,
    ← (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ).finrank_eq]
  exact (representationIntertwiningCompEquiv γ hγ ρ ρ).finrank_eq.symm

/-- The dimension of a simple module over its Schur endomorphism ring is
unchanged by surjective inflation. -/
theorem representationFinrankOverEnd_comp_eq
    [FiniteDimensional k V]
    (γ : D →* B) (hγ : Function.Surjective γ)
    (ρ : Representation k B V) [IsSimpleModule k[B] ρ.asModule] :
    Module.finrank (Module.End k[D]
        (inflatedRepresentation γ ρ).asModule)
        (inflatedRepresentation γ ρ).asModule =
      Module.finrank (Module.End k[B] ρ.asModule) ρ.asModule := by
  letI : IsSimpleModule k[D]
      (inflatedRepresentation γ ρ).asModule :=
    representation_comp_isSimpleModule γ hγ ρ
  have hend := representationEnd_finrank_comp_eq γ hγ ρ
  letI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[B] ρ.asModule
  have hD := schur_simple_finrank_tower
    (k := k) (R := k[D])
    (X := (inflatedRepresentation γ ρ).asModule)
  have hB := schur_simple_finrank_tower
    (k := k) (R := k[B]) (X := ρ.asModule)
  have hdim : Module.finrank k
      (inflatedRepresentation γ ρ).asModule =
      Module.finrank k ρ.asModule := by rfl
  rw [hD, hB, hend] at hdim
  apply Nat.eq_of_mul_eq_mul_left
    (Module.finrank_pos (R := k) (M := Module.End k[B] ρ.asModule))
  exact hdim

/-- Schur multiplicity of an arbitrary simple source and finite target is
unchanged when both representations are inflated along a surjective group
homomorphism. -/
theorem schurSocleMultiplicity_comp_eq_representation
    [FiniteDimensional k V] [FiniteDimensional k A]
    (γ : D →* B) (hγ : Function.Surjective γ)
    (ρ : Representation k B V) (σ : Representation k B A)
    [IsSimpleModule k[B] ρ.asModule]
    [IsSimpleModule k[D] (inflatedRepresentation γ ρ).asModule] :
    schurSocleMultiplicity
        (k := k) (R := k[D])
        (A := (inflatedRepresentation γ σ).asModule)
        (X := (inflatedRepresentation γ ρ).asModule) =
      schurSocleMultiplicity
        (k := k) (R := k[B])
        (A := σ.asModule) (X := ρ.asModule) := by
  letI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[B] ρ.asModule
  have hhom :=
    (representationIntertwiningCompEquiv γ hγ ρ σ).finrank_eq
  have hend :=
    (representationIntertwiningCompEquiv γ hγ ρ ρ).finrank_eq
  have hleft : Module.finrank k
      ((inflatedRepresentation γ ρ).IntertwiningMap
        (inflatedRepresentation γ σ)) =
      schurSocleMultiplicity
          (k := k) (R := k[D])
          (A := (inflatedRepresentation γ σ).asModule)
          (X := (inflatedRepresentation γ ρ).asModule) *
        Module.finrank k
          (Module.End k[D]
            (inflatedRepresentation γ ρ).asModule) := by
    rw [(Representation.IntertwiningMap.equivLinearMapAsModule
      (inflatedRepresentation γ ρ)
      (inflatedRepresentation γ σ)).finrank_eq]
    exact schurHom_finrank_eq_multiplicity
      (k := k) (R := k[D])
      (A := (inflatedRepresentation γ σ).asModule)
      (X := (inflatedRepresentation γ ρ).asModule)
  have hright : Module.finrank k (ρ.IntertwiningMap σ) =
      schurSocleMultiplicity
          (k := k) (R := k[B])
          (A := σ.asModule) (X := ρ.asModule) *
        Module.finrank k (Module.End k[B] ρ.asModule) := by
    rw [(Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).finrank_eq]
    exact schurHom_finrank_eq_multiplicity
      (k := k) (R := k[B]) (A := σ.asModule) (X := ρ.asModule)
  have hend' : Module.finrank k
      (Module.End k[D]
        (inflatedRepresentation γ ρ).asModule) =
      Module.finrank k (Module.End k[B] ρ.asModule) := by
    rw [← (Representation.IntertwiningMap.equivLinearMapAsModule
      (inflatedRepresentation γ ρ)
      (inflatedRepresentation γ ρ)).finrank_eq,
      ← (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ).finrank_eq]
    exact hend.symm
  rw [hright, hleft, hend'] at hhom
  apply Nat.eq_of_mul_eq_mul_right
    (Module.finrank_pos (R := k) (M := Module.End k[B] ρ.asModule))
  exact hhom.symm

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
    representationSchurCapacity (inflatedRepresentation γ σ) =
      representationSchurCapacity σ := by
  letI : Module k[D] σ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule
      (inflatedRepresentation γ σ)
  letI : IsScalarTower k k[D] σ.asModule :=
    inferInstanceAs
      (IsScalarTower k k[D]
        (Representation.asModule (inflatedRepresentation γ σ)))
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
    (Module.finrank k
      (ρ.IntertwiningMap (inflatedRepresentation γ σ)) : ℝ) ≤
      representationSchurCapacity σ * Module.finrank k V := by
  simpa only [representationSchurCapacity_comp γ hγ σ] using
    intertwiningMap_finrank_le_schur ρ
      (inflatedRepresentation γ σ)

/-- The finite-field cardinal estimate for the same literal Hom space. -/
theorem intertwiningMap_card_le_original_schur
    [Finite k] [FiniteDimensional k V] [FiniteDimensional k A]
    (γ : D →* B) (hγ : Function.Surjective γ)
    (ρ : Representation k D V) (σ : Representation k B A) :
    (Nat.card (ρ.IntertwiningMap
      (inflatedRepresentation γ σ)) : ℝ) ≤
      (Nat.card k : ℝ) ^ (representationSchurCapacity σ * Module.finrank k V) := by
  haveI : FiniteDimensional k
      (ρ.IntertwiningMap (inflatedRepresentation γ σ)) :=
    Module.Finite.equiv
      (Representation.IntertwiningMap.equivLinearMapAsModule ρ
        (inflatedRepresentation γ σ)).symm
  rw [Module.natCard_eq_pow_finrank (K := k), Nat.cast_pow, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast Nat.card_pos (α := k)
  · exact intertwiningMap_finrank_le_original_schur γ hγ ρ σ

end SymmetricSubgroupAsymptotics
