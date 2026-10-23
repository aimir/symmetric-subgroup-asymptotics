import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleParameterGeneration

/-! The four exact signed parameter charts generate the whole actual
original group. Equality on these charts therefore determines an
original automorphism; no source automorphism lift is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalParameterFaithful
open CFSGGTwoD4GeckSimpleParameters CFSGGTwoD4GeckOriginalSimpleParameters
open CFSGGTwoD4GeckOriginalProjection CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckSimpleParameterGeneration CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

theorem subgroup_eq_top_of_simple_parameters (H : Subgroup J)
    (hH : ∀ (neg a : Bool) (t : Multiplicative K), simpleGeneratedHom K neg a t ∈ H) : H = ⊤ := by
  have hle : J ≤ H.map (fixedRootGenerated K (RingEquiv.refl K)).subtype := by
    apply fixedRootGenerated_le_of_simple_parameters K (RingEquiv.refl K)
    · intro neg t _
      exact ⟨simpleGeneratedHom K neg false (Multiplicative.ofAdd t), hH neg false _, rfl⟩
    · intro neg t _
      exact ⟨simpleGeneratedHom K neg true (Multiplicative.ofAdd t), hH neg true _, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.property
  have he : y = x := Subtype.ext hyx
  exact he ▸ hy

theorem original_parameters_faithful [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
    (f g : MulAut (Projective CartanMatrix.G₂ K))
    (h : ∀ (neg a : Bool) (t : Multiplicative K),
      f (originalSimpleHom K neg a t) = g (originalSimpleHom K neg a t)) : f = g := by
  let H : Subgroup J := ((f.toMonoidHom).comp (generatedToOriginal K)).eqLocus
    ((g.toMonoidHom).comp (generatedToOriginal K))
  have hH : H = ⊤ := subgroup_eq_top_of_simple_parameters K H (by
    intro neg a t
    change f (originalSimpleHom K neg a t) = g (originalSimpleHom K neg a t)
    exact h neg a t)
  apply MulEquiv.ext
  intro x
  obtain ⟨u, rfl⟩ := generatedToOriginal_surjective K x
  have hu : u ∈ H := by rw [hH]; trivial
  exact hu

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalParameterFaithful
