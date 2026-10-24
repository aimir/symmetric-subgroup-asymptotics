import SymmetricSubgroupAsymptotics.CFSGSuzukiAbsoluteTrace
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-! The actual odd-dimensional prime-field quadratic form attached to
Suzuki squares. Its polar radical is precisely the prime-field line,
and that line is anisotropic. The true quadratic radical is therefore
zero even though the polar bilinear form is degenerate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSuzukiAbsoluteTraceQuadratic
open CFSGSuzukiFieldParameters CFSGSuzukiAbsoluteTrace
open FieldFunctionalMultiplicationDuality

def twistedPairing (m : ℕ) : LinearMap.BilinForm (ZMod 2) (Field m) :=
  (multiplicationFunctional (traceLinear m)).compl₂ (thetaAlgEquiv m).toLinearEquiv.toLinearMap

@[simp] theorem twistedPairing_apply (m : ℕ) (a b : Field m) :
    twistedPairing m a b = traceLinear m (a * theta m b) := rfl

def quadratic (m : ℕ) : QuadraticForm (ZMod 2) (Field m) :=
  (twistedPairing m).toQuadraticMap

@[simp] theorem quadratic_apply (m : ℕ) (a : Field m) :
    quadratic m a = traceLinear m (a * theta m a) := rfl

theorem polar_apply (m : ℕ) (a b : Field m) :
    (quadratic m).polarBilin a b =
      traceLinear m ((inverseTheta m a + theta m a) * b) := by
  rw [quadratic, LinearMap.BilinMap.polarBilin_toQuadraticMap]
  change traceLinear m (a * theta m b) + traceLinear m (b * theta m a) = _
  rw [trace_mul_theta, show b * theta m a = theta m a * b by ring, ← map_add, ← add_mul]

theorem polar_kernel_iff (m : ℕ) (a : Field m) :
    a ∈ (quadratic m).polarBilin.ker ↔ a = 0 ∨ a = 1 := by
  constructor
  · intro ha
    apply (inverseTheta_add_theta_eq_zero_iff m a).mp
    apply trace_product_separating m
    intro b
    have h := congrArg (fun l : Field m →ₗ[ZMod 2] ZMod 2 => l b) ha
    simpa only [polar_apply, LinearMap.zero_apply] using h
  · intro ha
    apply LinearMap.ext
    intro b
    rw [polar_apply, (inverseTheta_add_theta_eq_zero_iff m a).mpr ha, zero_mul, map_zero]
    rfl

@[simp] theorem quadratic_one (m : ℕ) : quadratic m 1 = 1 := by
  rw [quadratic_apply, map_one, mul_one, trace_one]

theorem quadratic_radical_eq_bot (m : ℕ) : (quadratic m).radical = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  obtain ⟨hq, hp⟩ := ha
  rcases (polar_kernel_iff m a).mp hp with hzero | hone
  · exact (Submodule.mem_bot (R := ZMod 2)).mpr hzero
  · subst a
    rw [quadratic_one] at hq
    exact (one_ne_zero hq).elim

end SymmetricSubgroupAsymptotics.CFSGSuzukiAbsoluteTraceQuadratic
