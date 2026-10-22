import SymmetricSubgroupAsymptotics.CFSGSymplecticPolarity
import SymmetricSubgroupAsymptotics.CFSGLinearFunctionalKernels
import SymmetricSubgroupAsymptotics.CFSGLinePreservingLinearMap

/-! An actual linear equivalence preserving all zero-pairing tests is
an alternating similitude. The multiplier is derived from literal
functionals, rather than supplied by a recognition hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticLinearSimilitudes
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K]

def pulledDual (n : ℕ) (e : (Index n → K) ≃ₗ[K] (Index n → K)) :
    (Index n → K) →ₗ[K] Module.Dual K (Index n → K) where
  toFun v := (pairingDual n (e v)).comp e.toLinearMap
  map_add' v w := by
    apply LinearMap.ext
    intro x
    change pairing n (e (v + w)) (e x) = pairing n (e v) (e x) + pairing n (e w) (e x)
    rw [map_add, pairing_add_left]
  map_smul' c v := by
    apply LinearMap.ext
    intro x
    change pairing n (e (c • v)) (e x) = c * pairing n (e v) (e x)
    rw [map_smul, pairing_smul_left]

theorem pulledDual_ne_zero (n : ℕ) (e : (Index n → K) ≃ₗ[K] (Index n → K))
    (v : Index n → K) (hv : v ≠ 0) : pulledDual n e v ≠ 0 := by
  have hev : e v ≠ 0 := by
    intro h
    exact hv (e.injective (h.trans e.map_zero.symm))
  obtain ⟨w, hw⟩ := exists_pairing_ne_zero n (e v) hev
  intro h
  have hh := congrArg (fun f : Module.Dual K (Index n → K) => f (e.symm w)) h
  change pairing n (e v) (e (e.symm w)) = 0 at hh
  exact hw (by simpa only [e.apply_symm_apply] using hh)

theorem exists_multiplier (n : ℕ) (hn : 0 < n)
    (e : (Index n → K) ≃ₗ[K] (Index n → K))
    (he : ∀ v w, pairing n (e v) (e w) = 0 ↔ pairing n v w = 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ v w, pairing n (e v) (e w) = c * pairing n v w := by
  let D := CFSGSymplecticPolarity.vectorDualEquiv K n
  let T : Module.End K (Index n → K) := D.symm.toLinearMap.comp (pulledDual n e)
  have hT (v : Index n → K) : ∃ c : K, T v = c • v := by
    by_cases hv : v = 0
    · subst v
      exact ⟨0, by rw [map_zero, zero_smul]⟩
    · obtain ⟨c, _, hc⟩ := CFSGLinearFunctionalKernels.nonzero_smul_of_zero_iff
        (pulledDual n e v) (pairingDual n v) (pulledDual_ne_zero n e v hv) (he v)
      refine ⟨c, ?_⟩
      apply D.injective
      change D (D.symm (pulledDual n e v)) = D (c • v)
      rw [D.apply_symm_apply, map_smul]
      exact hc
  obtain ⟨c, hc⟩ := CFSGLinePreservingLinearMap.exists_scalar T hT (Sum.inl ⟨0, hn⟩)
  have hform (v w : Index n → K) : pairing n (e v) (e w) = c * pairing n v w := by
    have hh := congrArg (fun L : Module.End K (Index n → K) => D (L v)) hc
    change D (D.symm (pulledDual n e v)) = D (c • v) at hh
    rw [D.apply_symm_apply, map_smul] at hh
    exact congrArg (fun f : Module.Dual K (Index n → K) => f w) hh
  refine ⟨c, ?_, hform⟩
  intro hz
  let v : Index n → K := Pi.single (Sum.inl ⟨0, hn⟩) 1
  have hv : v ≠ 0 := by
    intro h
    have hh := congrFun h (Sum.inl ⟨0, hn⟩)
    simp [v] at hh
  apply pulledDual_ne_zero n e v hv
  apply LinearMap.ext
  intro w
  change pairing n (e v) (e w) = 0
  rw [hform, hz, zero_mul]

end SymmetricSubgroupAsymptotics.CFSGSymplecticLinearSimilitudes
