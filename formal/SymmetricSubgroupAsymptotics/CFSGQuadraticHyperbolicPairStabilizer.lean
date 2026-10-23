import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.Ring

/-! A quadratic isometry fixing a literal hyperbolic pair acts by an
actual isometry on the SAME orthogonal tail. This is a coordinate
restriction lemma, valid in every characteristic and without a named
orthogonal-group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicPairStabilizer
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

theorem polar_first (Q : QuadraticForm K (K × (W × K))) (Q0 : QuadraticForm K W)
    (hform : ∀ a z b, Q (a, (z, b)) = a * b + Q0 z) (x : K × (W × K)) :
    Q.polarBilin x (1, (0, 0)) = x.2.2 := by
  rcases x with ⟨a, z, b⟩
  change Q ((a, (z, b)) + (1, (0, 0))) - Q (a, (z, b)) - Q (1, (0, 0)) = b
  simp only [Prod.mk_add_mk, add_zero, hform, QuadraticMap.map_zero]
  ring

theorem polar_second (Q : QuadraticForm K (K × (W × K))) (Q0 : QuadraticForm K W)
    (hform : ∀ a z b, Q (a, (z, b)) = a * b + Q0 z) (x : K × (W × K)) :
    Q.polarBilin x (0, (0, 1)) = x.1 := by
  rcases x with ⟨a, z, b⟩
  change Q ((a, (z, b)) + (0, (0, 1))) - Q (a, (z, b)) - Q (0, (0, 1)) = a
  simp only [Prod.mk_add_mk, add_zero, hform, QuadraticMap.map_zero]
  ring

theorem heads (Q : QuadraticForm K (K × (W × K))) (Q0 : QuadraticForm K W)
    (hform : ∀ a z b, Q (a, (z, b)) = a * b + Q0 z)
    (L : (K × (W × K)) ≃ₗ[K] (K × (W × K))) (hQ : ∀ x, Q (L x) = Q x)
    (he : L (1, (0, 0)) = (1, (0, 0))) (hf : L (0, (0, 1)) = (0, (0, 1)))
    (x : K × (W × K)) : (L x).1 = x.1 ∧ (L x).2.2 = x.2.2 := by
  have hB (u v : K × (W × K)) : Q.polarBilin (L u) (L v) = Q.polarBilin u v := by
    change Q (L u + L v) - Q (L u) - Q (L v) = Q (u + v) - Q u - Q v
    rw [← L.map_add, hQ, hQ, hQ]
  constructor
  · have h := hB x (0, (0, 1))
    rw [hf, polar_second Q Q0 hform, polar_second Q Q0 hform] at h
    exact h
  · have h := hB x (1, (0, 0))
    rw [he, polar_first Q Q0 hform, polar_first Q Q0 hform] at h
    exact h

def tailMap (L : (K × (W × K)) ≃ₗ[K] (K × (W × K))) : W →ₗ[K] W where
  toFun z := (L (0, (z, 0))).2.1
  map_add' z w := by
    simpa only [Prod.mk_add_mk, zero_add] using
      congrArg (fun x : K × (W × K) => x.2.1) (L.map_add (0, (z, 0)) (0, (w, 0)))
  map_smul' a z := by
    simpa only [Prod.smul_mk, smul_zero, RingHom.id_apply] using
      congrArg (fun x : K × (W × K) => x.2.1) (L.map_smul a (0, (z, 0)))

theorem tail_image (Q : QuadraticForm K (K × (W × K))) (Q0 : QuadraticForm K W)
    (hform : ∀ a z b, Q (a, (z, b)) = a * b + Q0 z)
    (L : (K × (W × K)) ≃ₗ[K] (K × (W × K))) (hQ : ∀ x, Q (L x) = Q x)
    (he : L (1, (0, 0)) = (1, (0, 0))) (hf : L (0, (0, 1)) = (0, (0, 1)))
    (z : W) : L (0, (z, 0)) = (0, (tailMap L z, 0)) := by
  have hh := heads Q Q0 hform L hQ he hf (0, (z, 0))
  exact Prod.ext hh.1 (Prod.ext rfl hh.2)

theorem exists_tail (Q : QuadraticForm K (K × (W × K))) (Q0 : QuadraticForm K W)
    (hform : ∀ a z b, Q (a, (z, b)) = a * b + Q0 z)
    (L : (K × (W × K)) ≃ₗ[K] (K × (W × K))) (hQ : ∀ x, Q (L x) = Q x)
    (he : L (1, (0, 0)) = (1, (0, 0))) (hf : L (0, (0, 1)) = (0, (0, 1))) :
    ∃ T : W ≃ₗ[K] W, (∀ z, Q0 (T z) = Q0 z) ∧
      ∀ a z b, L (a, (z, b)) = (a, (T z, b)) := by
  have hQi (x) : Q (L.symm x) = Q x := by
    have h := hQ (L.symm x)
    rw [L.apply_symm_apply] at h
    exact h.symm
  have hei : L.symm (1, (0, 0)) = (1, (0, 0)) := by
    apply L.injective
    rw [L.apply_symm_apply, he]
  have hfi : L.symm (0, (0, 1)) = (0, (0, 1)) := by
    apply L.injective
    rw [L.apply_symm_apply, hf]
  let T : W ≃ₗ[K] W :=
    { __ := tailMap L
      invFun := tailMap L.symm
      left_inv := fun z => by
        have h := L.symm_apply_apply (0, (z, 0))
        rw [tail_image Q Q0 hform L hQ he hf z] at h
        exact congrArg (fun x : K × (W × K) => x.2.1) h
      right_inv := fun z => by
        have h := L.apply_symm_apply (0, (z, 0))
        rw [tail_image Q Q0 hform L.symm hQi hei hfi z] at h
        exact congrArg (fun x : K × (W × K) => x.2.1) h }
  refine ⟨T, ?_, ?_⟩
  · intro z
    have h := hQ (0, (z, 0))
    rw [tail_image Q Q0 hform L hQ he hf z, hform, hform,
      zero_mul, zero_add] at h
    simpa only [zero_add] using h
  · intro a z b
    have hx : (a, (z, b)) = a • (1, (0, 0)) + (0, (z, 0)) + b • (0, (0, 1)) := by
      simp only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero, mul_zero,
        Prod.mk_add_mk, add_zero, zero_add]
    calc
      L (a, (z, b)) = L (a • (1, (0, 0)) + (0, (z, 0)) + b • (0, (0, 1))) := congrArg L hx
      _ = a • (1, (0, 0)) + (0, (tailMap L z, 0)) + b • (0, (0, 1)) := by
        rw [map_add, map_add, L.map_smul, L.map_smul, he, hf, tail_image Q Q0 hform L hQ he hf]
      _ = (a, (T z, b)) := by
        simp only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero, mul_zero,
          Prod.mk_add_mk, add_zero, zero_add]
        rfl

end SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicPairStabilizer
