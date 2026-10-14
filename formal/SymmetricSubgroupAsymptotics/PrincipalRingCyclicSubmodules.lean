import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Submodules of cyclic modules over principal ideal rings

The preimage of a submodule under the cyclic presentation R → M is
an ideal. Push its principal generator forward. Unlike the finite-free
PID argument, this cyclic case needs no domain or freeness hypothesis,
so it also applies to products of polynomial rings over fields.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace ModuleGeneratedBy

universe u

variable {R M : Type u} [CommRing R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M]

/-- Over any commutative principal ideal ring, every submodule of a
cyclic module is cyclic. Zero divisors in the coefficient ring are allowed. -/
theorem uniform_one_of_principalIdealRing (h : ModuleGeneratedBy R M 1)
    (W : Submodule R M) : ModuleGeneratedBy R W 1 := by
  obtain ⟨v, hv⟩ := h
  have hv0 : Submodule.span R ({v 0} : Set M) = ⊤ := by
    simpa only [Set.range_unique, Fin.default_eq_zero] using hv
  let F : R →ₗ[R] M := LinearMap.toSpanSingleton R M (v 0)
  have hF : Function.Surjective F := by
    apply LinearMap.range_eq_top.mp
    exact (LinearMap.range_toSpanSingleton (v 0)).trans hv0
  let I : Ideal R := W.comap F
  let a : R := Submodule.IsPrincipal.generator I
  have ha : F a ∈ W := Submodule.IsPrincipal.generator_mem I
  let w : W := ⟨F a, ha⟩
  refine ⟨fun _ ↦ w, top_unique ?_⟩
  intro x _
  obtain ⟨r, hr⟩ := hF x.1
  have hrI : r ∈ I := by
    change F r ∈ W
    rw [hr]
    exact x.property
  obtain ⟨s, hs⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hrI
  have hx : s • w = x := by
    apply Subtype.ext
    change s • F a = x.1
    calc
      s • F a = F (s • a) := (F.map_smul s a).symm
      _ = F r := congrArg F hs.symm
      _ = x.1 := hr
  rw [← hx]
  exact Submodule.smul_mem _ s (Submodule.subset_span ⟨0, rfl⟩)

end ModuleGeneratedBy
end SymmetricSubgroupAsymptotics

end
