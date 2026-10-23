import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-! Constructive lifting of a scalar span through an actual additive
image of a group homomorphism. Scalar multiples of the generators are
lifted individually; no scalar structure on the image subgroup, fixed
quotient lifting, or cohomology vanishing is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAdditiveImageScalarSpan
variable {F V G T : Type*} [Field F] [AddCommGroup V] [Module F V] [Group G]

theorem span_lifts (phi : G →* Multiplicative V) (v : T → V)
    (hlift : ∀ (a : F) (t : T), ∃ g : G, phi g = Multiplicative.ofAdd (a • v t))
    (x : V) (hx : x ∈ Submodule.span F (Set.range v)) :
    ∃ g : G, phi g = Multiplicative.ofAdd x := by
  have h : ∀ a : F, ∃ g : G, phi g = Multiplicative.ofAdd (a • x) := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨t, rfl⟩ := hy
      exact fun a => hlift a t
    | zero =>
      intro a
      refine ⟨1, ?_⟩
      rw [map_one, smul_zero]
      rfl
    | add y z _ _ hy hz =>
      intro a
      obtain ⟨g, hg⟩ := hy a
      obtain ⟨h, hh⟩ := hz a
      refine ⟨g*h, ?_⟩
      rw [map_mul, hg, hh, smul_add]
      rfl
    | smul b y _ hy =>
      intro a
      obtain ⟨g, hg⟩ := hy (a*b)
      refine ⟨g, ?_⟩
      rw [smul_smul]
      exact hg
  simpa only [one_smul] using h 1

end SymmetricSubgroupAsymptotics.CFSGAdditiveImageScalarSpan
