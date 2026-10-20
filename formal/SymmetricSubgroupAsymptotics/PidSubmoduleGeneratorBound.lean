import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Pi

/-!
# Submodules preserve the number of generators over a PID

Pull a submodule back along a finite free presentation. Smith normal form
supplies a basis for the pullback together with an embedding of its basis
indices into the original generator positions. Mapping that basis down and
padding by zero proves the bound without classifying torsion modules.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Every submodule of an `r`-generated module over a principal ideal domain
has a generating tuple with the same `r` positions. No finite-cardinality
or torsion hypothesis on the module is required. -/
theorem submodule_generatedBy_of_pid
    {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M]
    {r : ℕ} (v : Fin r → M)
    (hv : Submodule.span R (Set.range v) = ⊤)
    (W : Submodule R M) :
    ∃ w : Fin r → W, Submodule.span R (Set.range w) = ⊤ := by
  let b := Pi.basisFun R (Fin r)
  let F : (Fin r → R) →ₗ[R] M := b.constr R v
  have hF : Function.Surjective F := by
    apply LinearMap.range_eq_top.mp
    simpa only [F, Module.Basis.constr_range] using hv
  let U : Submodule R (Fin r → R) := W.comap F
  let q : U →ₗ[R] W :=
    (F.domRestrict U).codRestrict W (fun x ↦ x.property)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := hF y.1
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change F x ∈ W
    exact hx.symm ▸ y.property
  obtain ⟨m, snf⟩ := Submodule.smithNormalForm b U
  let c : Fin m → W := fun j ↦ q (snf.bN j)
  have hc : Submodule.span R (Set.range c) = ⊤ := by
    have hm := congrArg (Submodule.map q) snf.bN.span_eq
    rw [Submodule.map_span, Submodule.map_top,
      LinearMap.range_eq_top.mpr hq, ← Set.range_comp] at hm
    exact hm
  let w : Fin r → W := Function.extend snf.f c (fun _ ↦ 0)
  refine ⟨w, top_unique ?_⟩
  rw [← hc]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  refine ⟨snf.f j, ?_⟩
  exact snf.f.injective.extend_apply c (fun _ ↦ 0) j

end SymmetricSubgroupAsymptotics

end
