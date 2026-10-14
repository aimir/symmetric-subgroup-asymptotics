import SymmetricSubgroupAsymptotics.RepresentationPolynomialGeneratorBound

/-!
# Polynomial generator bounds from an element of the group algebra

A finite linear combination of acting operators preserves every
subrepresentation. The polynomial PID argument therefore applies to that
operator, with no requirement that it be a single group element.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra Polynomial

namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

theorem subrepresentation_algebraOperator_mem
    (rho : Representation k G V) (a : k[G]) (W : Subrepresentation rho)
    {v : V} (hv : v ∈ W) : rho.asAlgebraHom a v ∈ W := by
  have h := W.asSubmodule.smul_mem a
    (show rho.asModuleEquiv.symm v ∈ W.asSubmodule from hv)
  exact h

theorem subrepresentation_asAlgebraHom_restrict
    (rho : Representation k G V) (a : k[G]) (W : Subrepresentation rho) :
    W.toRepresentation.asAlgebraHom a =
      (rho.asAlgebraHom a).restrict
        (fun x hx ↦ subrepresentation_algebraOperator_mem rho a W (v := x) hx) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change (W.toRepresentation.asAlgebraHom a v : V) = rho.asAlgebraHom a v
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply, Submodule.coe_zero]
  | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply, Submodule.coe_add, ha, hb]
  | single g c =>
      simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply,
        Submodule.coe_smul_of_tower] <;> rfl

noncomputable def representationAlgebraPolynomialSubmodule
    (rho : Representation k G V) (a : k[G]) (W : Subrepresentation rho) :
    Submodule k[X] (Module.AEval' (rho.asAlgebraHom a)) :=
  Module.AEval.mapSubmodule k V (rho.asAlgebraHom a)
    ⟨W.toSubmodule, fun x hx ↦ subrepresentation_algebraOperator_mem rho a W (v := x) hx⟩

theorem mem_representationAlgebraPolynomialSubmodule
    (rho : Representation k G V) (a : k[G]) (W : Subrepresentation rho)
    (v : Module.AEval' (rho.asAlgebraHom a)) :
    v ∈ representationAlgebraPolynomialSubmodule rho a W ↔
      (Module.AEval'.of (rho.asAlgebraHom a)).symm v ∈ W :=
  Module.AEval.mem_mapSubmodule_apply k V (rho.asAlgebraHom a)

theorem representationGeneratedBy_of_algebraPolynomial
    (rho : Representation k G V) (a : k[G]) {n : ℕ}
    (v : Fin n → Module.AEval' (rho.asAlgebraHom a))
    (hv : Submodule.span k[X] (Set.range v) = ⊤) :
    RepresentationGeneratedBy rho n := by
  let w : Fin n → rho.asModule := fun j ↦
    rho.asModuleEquiv.symm ((Module.AEval'.of (rho.asAlgebraHom a)).symm (v j))
  let P : Submodule k[G] rho.asModule := Submodule.span k[G] (Set.range w)
  let S : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  let Q := representationAlgebraPolynomialSubmodule rho a S
  have hle : Submodule.span k[X] (Set.range v) ≤ Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply (mem_representationAlgebraPolynomialSubmodule rho a S (v j)).mpr
    change w j ∈ P
    exact Submodule.subset_span ⟨j, rfl⟩
  have hQ : Q = ⊤ := by
    rw [hv] at hle
    exact top_unique hle
  refine ⟨w, top_unique ?_⟩
  intro x _
  have hx : Module.AEval'.of (rho.asAlgebraHom a) (rho.asModuleEquiv x) ∈ Q := by
    rw [hQ]
    exact Submodule.mem_top
  have hm := (mem_representationAlgebraPolynomialSubmodule rho a S _).mp hx
  simpa only [LinearEquiv.symm_apply_apply] using hm

/-- An actual polynomial spanning tuple for any specified group-algebra
operator bounds every subrepresentation with the same number of generators. -/
theorem uniformSubrepresentationGeneratorBound_of_algebraPolynomial
    (rho : Representation k G V) (a : k[G]) {n : ℕ}
    (v : Fin n → Module.AEval' (rho.asAlgebraHom a))
    (hv : Submodule.span k[X] (Set.range v) = ⊤) :
    UniformSubrepresentationGeneratorBound rho n := by
  intro W
  let Q := representationAlgebraPolynomialSubmodule rho a W
  obtain ⟨w, hw⟩ := submodule_generatedBy_of_pid v hv Q
  let e : Module.AEval' (W.toRepresentation.asAlgebraHom a) ≃ₗ[k[X]] Q := by
    rw [subrepresentation_asAlgebraHom_restrict rho a W]
    exact Module.AEval.restrict_equiv_mapSubmodule (rho.asAlgebraHom a)
      W.toSubmodule
        (fun x hx ↦ subrepresentation_algebraOperator_mem rho a W (v := x) hx)
  let u : Fin n → Module.AEval' (W.toRepresentation.asAlgebraHom a) :=
    fun j ↦ e.symm (w j)
  have hu : Submodule.span k[X] (Set.range u) = ⊤ := by
    have hm := congrArg (Submodule.map e.symm.toLinearMap) hw
    rw [Submodule.map_span, Submodule.map_top,
      LinearMap.range_eq_top.mpr e.symm.surjective, ← Set.range_comp] at hm
    exact hm
  exact representationGeneratedBy_of_algebraPolynomial W.toRepresentation a u hu

end SymmetricSubgroupAsymptotics

end
