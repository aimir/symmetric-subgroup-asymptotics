import SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameters
import SymmetricSubgroupAsymptotics.FieldFunctionalMultiplicationDuality
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Tactic.FinCases

/-! Absolute trace on the actual odd-degree Suzuki coefficient field.
The trace of one is one, so division gives surjectivity of every nonzero
multiplication pairing.  The defining twist and its inverse preserve
this same prime-field trace. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSuzukiAbsoluteTrace
open CFSGSuzukiFieldParameters

def traceLinear (m : ℕ) : Field m →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) (Field m)

theorem field_finrank (m : ℕ) : Module.finrank (ZMod 2) (Field m) = 2*m+1 :=
  GaloisField.finrank 2 (by omega)

theorem trace_algebraMap (m : ℕ) (c : ZMod 2) :
    traceLinear m (algebraMap (ZMod 2) (Field m) c) = c := by
  change Algebra.trace (ZMod 2) (Field m) (algebraMap (ZMod 2) (Field m) c) = c
  rw [Algebra.trace_algebraMap, field_finrank]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add, one_mul]

@[simp] theorem trace_one (m : ℕ) : traceLinear m 1 = 1 := by
  simpa only [map_one] using trace_algebraMap m 1

theorem traceLinear_surjective (m : ℕ) : Function.Surjective (traceLinear m) :=
  fun c => ⟨algebraMap (ZMod 2) (Field m) c, trace_algebraMap m c⟩

theorem traceLinear_ne_zero (m : ℕ) : traceLinear m ≠ 0 := by
  intro h
  have he := congrArg (fun l : Field m →ₗ[ZMod 2] ZMod 2 => l 1) h
  change traceLinear m 1 = 0 at he
  rw [trace_one] at he
  exact one_ne_zero he

def thetaAlgEquiv (m : ℕ) : Field m ≃ₐ[ZMod 2] Field m :=
  AlgEquiv.ofRingEquiv (f := thetaEquiv m) (by
    intro c
    change theta m (algebraMap (ZMod 2) (Field m) c) = algebraMap (ZMod 2) (Field m) c
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl <;> simp only [map_zero, map_one])

theorem trace_theta (m : ℕ) (x : Field m) :
    traceLinear m (theta m x) = traceLinear m x :=
  Algebra.trace_eq_of_algEquiv (thetaAlgEquiv m) x

theorem trace_inverseTheta (m : ℕ) (x : Field m) :
    traceLinear m (inverseTheta m x) = traceLinear m x := by
  have h := trace_theta m (inverseTheta m x)
  rw [theta_inverseTheta] at h
  exact h.symm

theorem trace_mul_theta (m : ℕ) (a b : Field m) :
    traceLinear m (a * theta m b) = traceLinear m (inverseTheta m a * b) := by
  have h := trace_theta m (inverseTheta m a * b)
  rw [map_mul, theta_inverseTheta] at h
  exact h

theorem trace_product_surjective (m : ℕ) (a : Field m) (ha : a ≠ 0) :
    Function.Surjective (fun b : Field m => traceLinear m (a * b)) := by
  intro c
  obtain ⟨u, hu⟩ := traceLinear_surjective m c
  refine ⟨u / a, ?_⟩
  change traceLinear m (a * (u / a)) = c
  rw [show a * (u / a) = u by field_simp]
  exact hu

theorem trace_product_separating (m : ℕ) (a : Field m)
    (h : ∀ b : Field m, traceLinear m (a * b) = 0) : a = 0 := by
  by_contra ha
  obtain ⟨b, hb⟩ := trace_product_surjective m a ha 1
  exact one_ne_zero (hb.symm.trans (h b))

theorem inverseTheta_add_theta_eq_zero_iff (m : ℕ) (a : Field m) :
    inverseTheta m a + theta m a = 0 ↔ a = 0 ∨ a = 1 := by
  constructor
  · intro h
    have he : a + a^2 = 0 := by
      have hh := congrArg (theta m) h
      simpa only [map_add, map_zero, theta_inverseTheta, theta_twice] using hh
    have hs : a^2 = a := by
      have hh := eq_neg_of_add_eq_zero_left he
      simpa only [CharTwo.neg_eq] using hh.symm
    have hz : a * (a - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, hs, sub_self]
    exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp
  · rintro (rfl | rfl) <;> simp only [map_zero, map_one, CharTwo.add_self_eq_zero]

end SymmetricSubgroupAsymptotics.CFSGSuzukiAbsoluteTrace
