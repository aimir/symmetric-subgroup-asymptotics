import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.NormalImageKernelGeneratorTransfer

/-! A displayed linear semidirect product inherits a uniform normal
generator bound when every nonidentity complement element has surjective
difference from the identity. Commutators with one such lift force the
entire original translation kernel. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace FixedPointFreeSemidirectNormalGenerators

open SemidirectProduct LinearSemidirectCoprimeSocleBounds

variable {p : ℕ} [Fact p.Prime]
  {R V : Type} [Group R] [Finite R] [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V]
  (rho : R →* (V ≃ₗ[ZMod p] V))

theorem kernel_cover
    (hdiff : ∀ r : R, r ≠ 1 → Function.Surjective (fun v : V => rho r v - v))
    (N : Subgroup (Model rho)) (hN : N.Normal)
    (hNE : ¬ N ≤ translationKernel rho) : translationKernel rho ≤ N := by
  obtain ⟨g, hgN, hgE⟩ := Set.not_subset.mp hNE
  have hgr : g.right ≠ 1 := hgE
  intro e he
  obtain ⟨v, hv⟩ := hdiff g.right hgr e.left.toAdd
  let t : Model rho := inl (Multiplicative.ofAdd v)
  have hc : g * t * g⁻¹ * t⁻¹ ∈ N := by
    have h := hN.conj_mem g⁻¹ (N.inv_mem hgN) t
    simpa only [mul_assoc] using N.mul_mem hgN h
  have hcomm : g * t * g⁻¹ * t⁻¹ = e := by
    dsimp only [t]
    rw [conjugate_translation, ← map_inv, ← map_mul]
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change rho g.right v + -v = e.left.toAdd
      simpa only [sub_eq_add_neg] using hv
    · exact (show e.right = 1 from he).symm
  exact hcomm ▸ hc

theorem normalGen_le {t : ℕ}
    (huniform : UniformSubrepresentationGeneratorBound (linearRepresentation rho) t)
    (hR : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ t)
    (hdiff : ∀ r : R, r ≠ 1 → Function.Surjective (fun v : V => rho r v - v))
    (N : Subgroup (Model rho)) [N.Normal] : MarkedC4.normalGen N ≤ t := by
  by_cases hNE : N ≤ translationKernel rho
  · exact ElementaryUniformNormalGenerators.kernel_normalGen_le
      (translationKernel rho) (translationChart rho) t
      (LinearSemidirectUniformNormalGenerators.translationRepresentation_uniform rho huniform)
      N hNE
  · let pi : Model rho →* R := SemidirectProduct.rightHom
    have hpi : Function.Surjective pi := rightHom_surjective
    exact normalGen_le_of_kernel_cover_outside pi hpi (translationKernel rho) le_rfl
      (kernel_cover rho hdiff) N hNE
      (hR (N.map pi) ((inferInstance : N.Normal).map pi hpi))

end FixedPointFreeSemidirectNormalGenerators
end SymmetricSubgroupAsymptotics

end
