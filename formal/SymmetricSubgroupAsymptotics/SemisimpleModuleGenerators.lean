import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators
import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Generators of a finite semisimple module from its isotypic rows

For a finite semisimple `R`-module, distinct isotypic components can use
the same generator positions.  The proof below keeps this sharing literal.
For each component, pad a generating tuple to the common length and add
the tuples coordinatewise.  The central projector onto one isotypic
component belongs to the double centralizer.  Jacobson density therefore
realizes that projector on the finite tuple by an element of `R`, recovering
the component tuple from the packed tuple.

Together with `SchurIsotypicGenerators`, this is the usual semisimple
generator criterion with the Schur-division-ring denominator retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

universe u

section CentralProjector

variable {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
  [IsSemisimpleModule R M] [Module.Finite R M]

private local instance : DecidableEq (isotypicComponents R M) :=
  Classical.decEq _

/-- The dependent coordinate tuple which is the identity at `c` and zero
at every other isotypic component. -/
private noncomputable def isotypicCoordinateProjector
    (c : isotypicComponents R M) :
    ∀ d : isotypicComponents R M, Module.End R d.1 :=
  Pi.single c (1 : Module.End R c.1)

/-- The central idempotent which is one on `c` and zero on every other
isotypic component.  It is defined through Mathlib's literal product
decomposition of the endomorphism ring. -/
private noncomputable def isotypicCentralProjector
    (c : isotypicComponents R M) : Module.End R M :=
  (IsSemisimpleModule.endRingEquiv R M).symm
    (isotypicCoordinateProjector (R := R) (M := M) c)

omit [Module.Finite R M] in
private theorem isotypicCentralProjector_coordinates
    (c d : isotypicComponents R M) :
    (IsSemisimpleModule.endRingEquiv R M)
        (isotypicCentralProjector (R := R) (M := M) c) d =
      isotypicCoordinateProjector (R := R) (M := M) c d := by
  exact congrFun ((IsSemisimpleModule.endRingEquiv R M).apply_symm_apply
    (isotypicCoordinateProjector (R := R) (M := M) c)) d

omit [Module.Finite R M] in
/-- The projector is the identity on its selected component. -/
private theorem isotypicCentralProjector_apply_of_mem
    (c : isotypicComponents R M) {x : M} (hx : x ∈ c.1) :
    isotypicCentralProjector (R := R) (M := M) c x = x := by
  have hcoord := isotypicCentralProjector_coordinates
    (R := R) (M := M) c c
  rw [isotypicCoordinateProjector, Pi.single_eq_same] at hcoord
  have happ := LinearMap.congr_fun hcoord ⟨x, hx⟩
  exact congrArg Subtype.val happ

omit [Module.Finite R M] in
/-- The projector kills every other isotypic component. -/
private theorem isotypicCentralProjector_apply_of_mem_of_ne
    (c d : isotypicComponents R M) (hcd : c ≠ d)
    {x : M} (hx : x ∈ d.1) :
    isotypicCentralProjector (R := R) (M := M) c x = 0 := by
  have hcoord := isotypicCentralProjector_coordinates
    (R := R) (M := M) c d
  have happ := LinearMap.congr_fun hcoord ⟨x, hx⟩
  have hdc : d ≠ c := fun h ↦ hcd h.symm
  have hp0 : isotypicCoordinateProjector (R := R) (M := M) c d = 0 := by
    exact Pi.single_eq_of_ne hdc _
  rw [hp0] at happ
  have hv := congrArg Subtype.val happ
  simpa only [IsSemisimpleModule.endRingEquiv,
    IsSemisimpleModule.endAlgEquiv, iSupIndep.algEquiv,
    iSupIndep.ringEquiv, LinearMap.zero_apply] using hv

omit [Module.Finite R M] in
/-- The component projector is central in the whole `R`-endomorphism
ring. -/
private theorem isotypicCentralProjector_commute
    (c : isotypicComponents R M) (f : Module.End R M) :
    isotypicCentralProjector (R := R) (M := M) c * f =
      f * isotypicCentralProjector (R := R) (M := M) c := by
  apply (IsSemisimpleModule.endRingEquiv R M).injective
  apply funext
  intro d
  rw [map_mul, map_mul]
  by_cases hdc : d = c
  · subst d
    have hp := isotypicCentralProjector_coordinates
      (R := R) (M := M) c c
    let fc : Module.End R c.1 :=
      (IsSemisimpleModule.endRingEquiv R M) f c
    change ((IsSemisimpleModule.endRingEquiv R M)
        (isotypicCentralProjector (R := R) (M := M) c) c) * fc =
      fc * ((IsSemisimpleModule.endRingEquiv R M)
        (isotypicCentralProjector (R := R) (M := M) c) c)
    rw [hp]
    simp only [isotypicCoordinateProjector, Pi.single_eq_same,
      one_mul, mul_one]
  · have hp := isotypicCentralProjector_coordinates
      (R := R) (M := M) c d
    let fd : Module.End R d.1 :=
      (IsSemisimpleModule.endRingEquiv R M) f d
    change ((IsSemisimpleModule.endRingEquiv R M)
        (isotypicCentralProjector (R := R) (M := M) c) d) * fd =
      fd * ((IsSemisimpleModule.endRingEquiv R M)
        (isotypicCentralProjector (R := R) (M := M) c) d)
    have hp0 : isotypicCoordinateProjector (R := R) (M := M) c d = 0 := by
      exact Pi.single_eq_of_ne hdc _
    rw [hp, hp0, zero_mul, mul_zero]

/-- The same central projector, regarded as an endomorphism over the full
endomorphism ring.  This is the exact input type of Jacobson density. -/
private noncomputable def isotypicCentralProjectorDouble
    (c : isotypicComponents R M) :
    Module.End (Module.End R M) M where
  toFun := isotypicCentralProjector (R := R) (M := M) c
  map_add' := map_add _
  map_smul' f x := by
    change isotypicCentralProjector (R := R) (M := M) c (f x) =
      f (isotypicCentralProjector (R := R) (M := M) c x)
    exact DFunLike.congr_fun
      (isotypicCentralProjector_commute (R := R) (M := M) c f) x

end CentralProjector

section ComponentSharing

variable {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
  [IsSemisimpleModule R M] [Module.Finite R M]

/-- If every isotypic component admits a generating tuple of length `t`,
then the entire finite semisimple module admits one tuple of the same
length.  Thus distinct simple types take a maximum, rather than a sum. -/
theorem semisimple_moduleGeneratedBy_of_isotypicComponents
    (t : ℕ)
    (hcomponent : ∀ c : isotypicComponents R M,
      ModuleGeneratedBy R c.1 t) :
    ModuleGeneratedBy R M t := by
  classical
  choose v hv using hcomponent
  let packed : Fin t → M := fun a ↦
    ∑ c : isotypicComponents R M, (v c a : M)
  let W : Submodule R M := Submodule.span R (Set.range packed)
  have hproject (c : isotypicComponents R M) (a : Fin t) :
      isotypicCentralProjector (R := R) (M := M) c (packed a) =
        (v c a : M) := by
    dsimp only [packed]
    rw [map_sum, Finset.sum_eq_single c]
    · exact isotypicCentralProjector_apply_of_mem
        (R := R) (M := M) c (v c a).2
    · intro d _hd hdc
      exact isotypicCentralProjector_apply_of_mem_of_ne
        (R := R) (M := M) c d (fun h ↦ hdc h.symm) (v d a).2
    · intro hc
      exact (hc (Finset.mem_univ c)).elim
  have hseed (c : isotypicComponents R M) (a : Fin t) :
      (v c a : M) ∈ W := by
    let s : Finset M := Finset.univ.image packed
    obtain ⟨r, hr⟩ := jacobson_density
      (isotypicCentralProjectorDouble (R := R) (M := M) c) s
    have hmem : packed a ∈ s :=
      Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
    have hr' := hr (packed a) hmem
    change isotypicCentralProjector (R := R) (M := M) c (packed a) =
      r • packed a at hr'
    rw [← hproject c a, hr']
    exact W.smul_mem r
      (Submodule.subset_span (Set.mem_range_self a))
  have hcomponent_le (c : isotypicComponents R M) : c.1 ≤ W := by
    let Wc : Submodule R c.1 := W.comap c.1.subtype
    have hspan : Submodule.span R (Set.range (v c)) ≤ Wc := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact hseed c a
    rw [hv c] at hspan
    intro x hx
    exact hspan
      (show (⟨x, hx⟩ : c.1) ∈ (⊤ : Submodule R c.1) from trivial)
  refine ⟨packed, top_unique ?_⟩
  rw [← sSup_isotypicComponents R M]
  exact sSup_le fun c hc ↦ hcomponent_le ⟨c, hc⟩

end ComponentSharing

section SchurCriterion

variable {k R M : Type u} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [FiniteDimensional k M] [IsSemisimpleModule R M]

/-- Numerical Schur-multiplicity criterion for generation of a finite
semisimple module.  The denominator is the dimension of the simple module
over its literal Schur division ring. -/
theorem semisimple_moduleGeneratedBy_of_schurMultiplicity_le
    (t : ℕ)
    (hmul : ∀ S : Submodule R M, [IsSimpleModule R S] →
      schurSocleMultiplicity (k := k) (R := R) (A := M) (X := S) ≤
        t * Module.finrank (Module.End R S) S) :
    ModuleGeneratedBy R M t := by
  classical
  letI : Module.Finite R M :=
    Module.Finite.of_restrictScalars_finite k R M
  apply semisimple_moduleGeneratedBy_of_isotypicComponents t
  intro c
  obtain ⟨S, hS, hc⟩ := c.2
  letI : IsSimpleModule R S := hS
  letI : FiniteDimensional k S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars k) S.subtype_injective
  letI : Module.Finite (Module.End R S) S :=
    Module.Finite.of_restrictScalars_finite k (Module.End R S) S
  rw [hc]
  apply ModuleGeneratedBy.congr
    (schurSocleDecomposition
      (k := k) (R := R) (A := M) (X := S)).symm
  exact schurPi_moduleGeneratedBy _ t (hmul S)

/-- Ratio form of the Schur criterion.  This is convenient for Frobenius
reciprocity: an upper bound on every simple-source Hom density immediately
gives an actual generating tuple for the semisimple target. -/
theorem semisimple_moduleGeneratedBy_of_schurRatio_le
    (t : ℕ)
    (hratio : ∀ S : Submodule R M, [IsSimpleModule R S] →
      (Module.finrank k (S →ₗ[R] M) : ℝ) /
          Module.finrank k S ≤ t) :
    ModuleGeneratedBy R M t := by
  apply semisimple_moduleGeneratedBy_of_schurMultiplicity_le
    (k := k) (R := R) (M := M) t
  intro S hS
  letI : IsSimpleModule R S := hS
  letI : Nontrivial S := IsSimpleModule.nontrivial R S
  letI : FiniteDimensional k S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars k) S.subtype_injective
  have hSpos : (0 : ℝ) < Module.finrank k S := by
    exact_mod_cast (Module.finrank_pos (R := k) (M := S))
  have hreal : (Module.finrank k (S →ₗ[R] M) : ℝ) ≤
      (t : ℝ) * Module.finrank k S :=
    (div_le_iff₀ hSpos).mp (hratio S)
  have hnat : Module.finrank k (S →ₗ[R] M) ≤
      t * Module.finrank k S := by
    exact_mod_cast hreal
  rw [schurHom_finrank_eq_multiplicity,
    schur_simple_finrank_tower (k := k) (R := R) (X := S)] at hnat
  have hfactor :
      Module.finrank k (Module.End R S) *
          schurSocleMultiplicity (k := k) (R := R) (A := M) (X := S) ≤
        Module.finrank k (Module.End R S) *
          (t * Module.finrank (Module.End R S) S) := by
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hnat
  exact Nat.le_of_mul_le_mul_left hfactor
    (Module.finrank_pos (R := k) (M := Module.End R S))

end SchurCriterion

section RepresentationCriterion

variable {k G V : Type u} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- A semisimple representation whose intrinsic Schur capacity is at most
the integer `t` is actually generated by `t` vectors. -/
theorem semisimple_representationGeneratedBy_of_schurCapacity_le
    (sigma : Representation k G V)
    [FiniteDimensional k V]
    [IsSemisimpleModule k[G] sigma.asModule]
    (t : ℕ)
    (hcap : representationSchurCapacity sigma ≤ t) :
    RepresentationGeneratedBy sigma t := by
  letI : Module k[G] sigma.asModule :=
    Representation.instModuleMonoidAlgebraAsModule sigma
  letI : IsScalarTower k k[G] sigma.asModule :=
    inferInstanceAs (IsScalarTower k k[G] (Representation.asModule sigma))
  have hgen : ModuleGeneratedBy k[G] sigma.asModule t := by
    apply semisimple_moduleGeneratedBy_of_schurRatio_le
      (k := k) (R := k[G]) t
    intro S hS
    letI : IsSimpleModule k[G] S := hS
    exact (le_csSup
      (schurCapacity_bddAbove (k := k) (R := k[G])
        (A := sigma.asModule))
      (Set.mem_insert_of_mem 0 ⟨S, hS, rfl⟩)).trans hcap
  simpa only [ModuleGeneratedBy, RepresentationGeneratedBy] using hgen

end RepresentationCriterion

end SymmetricSubgroupAsymptotics

end
