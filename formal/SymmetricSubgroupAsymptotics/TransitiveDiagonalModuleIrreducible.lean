import SymmetricSubgroupAsymptotics.DistinctDiagonalFullCoordinateModule
import Mathlib.RepresentationTheory.Irreducible

/-!
# Irreducibility from transitive coordinates and a separating diagonal kernel

This is the reusable algebra behind the four-distinct-sign affine branch.
A representation is written in coordinates whose one-dimensional factors
can be moved transitively.  A subgroup acts diagonally, with a different
character on every coordinate.  Every nonzero invariant subspace therefore
projects nontrivially, hence surjectively, onto every coordinate; the
distinct-character projector then recovers every single-coordinate vector.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DiagonalInvariantSubmodules

variable {k ι G J M V : Type*}
  [Field k] [Fintype ι]
  [Group G] [Group J]
  [AddCommGroup M] [Module k M] [Nontrivial M]
  [AddCommGroup V] [Module k V]

/-- A transitive monomial representation with a separating diagonal
subgroup is irreducible when the coordinate module is one-dimensional.

The `coordinate_transport` premise deliberately records only preservation
of a nonzero coordinate.  This avoids choosing scalar matrices for the
non-diagonal elements and exactly matches the literal wreath-coordinate
formula used by the affine application. -/
theorem irreducible_of_transitive_diagonal_coordinates
    (rho : Representation k G M)
    (coordinates : M ≃ₗ[k] (ι → V))
    (diagonalSource : J →* G)
    (scalar : ι → J → k)
    (scalar_injective : Function.Injective scalar)
    (diagonal_action : ∀ (g : J) (x : M),
      coordinates (rho (diagonalSource g) x) =
        diagonalModuleOperator scalar g (coordinates x))
    (coordinate_transport : ∀ (x : M) (i j : ι),
      coordinates x i ≠ 0 →
        ∃ g : G, coordinates (rho g x) j ≠ 0)
    (coordinate_finrank : Module.finrank k V = 1) :
    Representation.IsIrreducible rho := by
  have hbot_top : (⊥ : Subrepresentation rho) ≠ ⊤ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    intro h
    have hxmem : x ∈ (⊥ : Subrepresentation rho) := by
      rw [h]
      trivial
    change x ∈ (⊥ : Submodule k M) at hxmem
    exact hx ((Submodule.mem_bot (R := k)).mp hxmem)
  letI : Nontrivial (Subrepresentation rho) := ⟨⟨⊥, ⊤, hbot_top⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    let f : M →ₗ[k] (ι → V) := coordinates.toLinearMap
    let K₀ : Submodule k (ι → V) := W.toSubmodule.map f
    let K : ModuleStable (V := V) scalar := by
      refine ⟨K₀, ?_⟩
      intro g y hy
      rcases hy with ⟨x, hxW, rfl⟩
      refine ⟨rho (diagonalSource g) x,
        W.apply_mem_toSubmodule (diagonalSource g) hxW, ?_⟩
      exact diagonal_action g x
    have hWsub : W.toSubmodule ≠ ⊥ := by
      intro h
      apply hW
      apply Subrepresentation.toSubmodule_injective
      exact h
    obtain ⟨x, hxW, hx⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hWsub
    have hcoordinate : ∃ i : ι, coordinates x i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      apply hx
      apply coordinates.injective
      funext i
      simpa only [map_zero] using h i
    obtain ⟨i₀, hi₀⟩ := hcoordinate
    have hfull : ModuleFullCoordinates K₀ := by
      intro j z
      obtain ⟨g, hg⟩ := coordinate_transport x i₀ j hi₀
      let y : K₀ := ⟨coordinates (rho g x),
        ⟨rho g x, W.apply_mem_toSubmodule g hxW, rfl⟩⟩
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
        coordinate_finrank hg z
      refine ⟨c • y, ?_⟩
      change c • coordinates (rho g x) j = z
      exact hc
    have hKtop : K₀ = ⊤ :=
      eq_top_of_moduleFullCoordinates_of_injective scalar scalar_injective
        K hfull
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro x _hx
    have hxK : coordinates x ∈ K₀ := by
      rw [hKtop]
      exact Submodule.mem_top
    rcases hxK with ⟨y, hyW, hy⟩
    have hy' : coordinates y = coordinates x := by
      simpa only [f] using hy
    have hyx : y = x := coordinates.injective hy'
    simpa only [hyx] using hyW

end DiagonalInvariantSubmodules
end SymmetricSubgroupAsymptotics

end
