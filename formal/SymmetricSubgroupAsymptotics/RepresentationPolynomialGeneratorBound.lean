import SymmetricSubgroupAsymptotics.PidSubmoduleGeneratorBound
import SymmetricSubgroupAsymptotics.InducedSubrepresentationCount
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Uniform representation generators from a polynomial action

Fix one acting element. Its linear operator makes the representation a
module over the polynomial ring. Every group-invariant subspace is a
polynomial submodule. The PID generator theorem therefore upgrades an
ambient polynomial generating tuple to a uniform group-module bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra Polynomial

namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- Regard an actual invariant subspace as a polynomial submodule for one
specified acting element. -/
noncomputable def representationElementPolynomialSubmodule
    (rho : Representation k G V) (g : G) (W : Subrepresentation rho) :
    Submodule k[X] (Module.AEval' (rho g)) :=
  Module.AEval.mapSubmodule k V (rho g)
    ⟨W.toSubmodule, W.apply_mem_toSubmodule g⟩

/-- The polynomial submodule has exactly the original underlying vectors. -/
theorem mem_representationElementPolynomialSubmodule
    (rho : Representation k G V) (g : G) (W : Subrepresentation rho)
    (v : Module.AEval' (rho g)) :
    v ∈ representationElementPolynomialSubmodule rho g W ↔
      (Module.AEval'.of (rho g)).symm v ∈ W :=
  Module.AEval.mem_mapSubmodule_apply k V (rho g)

/-- Polynomial generation by one acting operator implies generation by the
full group algebra, with the same tuple length. -/
theorem representationGeneratedBy_of_polynomial
    (rho : Representation k G V) (g : G) {n : ℕ}
    (v : Fin n → Module.AEval' (rho g))
    (hv : Submodule.span k[X] (Set.range v) = ⊤) :
    RepresentationGeneratedBy rho n := by
  let w : Fin n → rho.asModule := fun j ↦
    rho.asModuleEquiv.symm ((Module.AEval'.of (rho g)).symm (v j))
  let P : Submodule k[G] rho.asModule := Submodule.span k[G] (Set.range w)
  let S : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  let Q := representationElementPolynomialSubmodule rho g S
  have hle : Submodule.span k[X] (Set.range v) ≤ Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply (mem_representationElementPolynomialSubmodule rho g S (v j)).mpr
    change w j ∈ P
    exact Submodule.subset_span ⟨j, rfl⟩
  have hQ : Q = ⊤ := by
    rw [hv] at hle
    exact top_unique hle
  refine ⟨w, top_unique ?_⟩
  intro x _
  have hx : Module.AEval'.of (rho g) (rho.asModuleEquiv x) ∈ Q := by
    rw [hQ]
    exact Submodule.mem_top
  have hm := (mem_representationElementPolynomialSubmodule rho g S _).mp hx
  simpa only [LinearEquiv.symm_apply_apply] using hm

/-- The polynomial ring is a PID, so an ambient `n`-generator polynomial
module bounds every actual group-invariant subspace by the same `n`. -/
theorem uniformSubrepresentationGeneratorBound_of_polynomial
    (rho : Representation k G V) (g : G) {n : ℕ}
    (v : Fin n → Module.AEval' (rho g))
    (hv : Submodule.span k[X] (Set.range v) = ⊤) :
    UniformSubrepresentationGeneratorBound rho n := by
  intro W
  let Q := representationElementPolynomialSubmodule rho g W
  obtain ⟨w, hw⟩ := submodule_generatedBy_of_pid v hv Q
  let e : Module.AEval' (W.toRepresentation g) ≃ₗ[k[X]] Q :=
    Module.AEval.restrict_equiv_mapSubmodule (rho g) W.toSubmodule
      (W.apply_mem_toSubmodule g)
  let u : Fin n → Module.AEval' (W.toRepresentation g) := fun j ↦ e.symm (w j)
  have hu : Submodule.span k[X] (Set.range u) = ⊤ := by
    have hm := congrArg (Submodule.map e.symm.toLinearMap) hw
    rw [Submodule.map_span, Submodule.map_top,
      LinearMap.range_eq_top.mpr e.symm.surjective, ← Set.range_comp] at hm
    exact hm
  exact representationGeneratedBy_of_polynomial W.toRepresentation g u hu

end SymmetricSubgroupAsymptotics

end
