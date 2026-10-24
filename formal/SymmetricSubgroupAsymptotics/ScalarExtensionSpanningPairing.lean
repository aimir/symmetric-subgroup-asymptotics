import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! Nondegeneracy descends to a base-field space whose actual image spans
the ambient extension-field space. No averaging by the extension degree
or trace normalization is used, so the extension degree may be zero in
the characteristic. The scalar-valued base pairing is supplied together
with its actual compatibility with the ambient pairing. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.ScalarExtensionSpanningPairing

variable {F K V M : Type*} [Field F] [Field K] [Algebra F K]
variable [AddCommGroup V] [Module F V] [AddCommGroup M]
variable [Module F M] [Module K M]

theorem separating_of_spanning_image
    (B : V →ₗ[F] V →ₗ[F] F) (BK : M →ₗ[K] M →ₗ[K] K)
    (e : V →ₗ[F] M) (he : Function.Injective e)
    (hspan : Submodule.span K (Set.range e) = ⊤)
    (hcompat : ∀ v w, BK (e v) (e w) = algebraMap F K (B v w))
    (hBK : ∀ x, (∀ y, BK x y = 0) → x = 0) :
    ∀ v, (∀ w, B v w = 0) → v = 0 := by
  intro v hv
  have hker : Submodule.span K (Set.range e) ≤ (BK (e v)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    change BK (e v) (e w) = 0
    rw [hcompat, hv w, map_zero]
  have hz : e v = 0 := hBK (e v) (fun y => hker (by rw [hspan]; trivial))
  apply he
  simpa only [map_zero] using hz

theorem surjective_of_spanning_image
    (B : V →ₗ[F] V →ₗ[F] F) (BK : M →ₗ[K] M →ₗ[K] K)
    (e : V →ₗ[F] M) (he : Function.Injective e)
    (hspan : Submodule.span K (Set.range e) = ⊤)
    (hcompat : ∀ v w, BK (e v) (e w) = algebraMap F K (B v w))
    (hBK : ∀ x, (∀ y, BK x y = 0) → x = 0)
    (v : V) (hv : v ≠ 0) : Function.Surjective (B v) := by
  have hn : ∃ w, B v w ≠ 0 := by
    by_contra hn
    apply hv
    apply separating_of_spanning_image B BK e he hspan hcompat hBK v
    intro w
    exact not_not.mp (fun hw => hn ⟨w, hw⟩)
  obtain ⟨w, hw⟩ := hn
  intro a
  refine ⟨(a / B v w) • w, ?_⟩
  rw [map_smul]
  change (a / B v w) * B v w = a
  exact div_mul_cancel₀ a hw

end SymmetricSubgroupAsymptotics.ScalarExtensionSpanningPairing
