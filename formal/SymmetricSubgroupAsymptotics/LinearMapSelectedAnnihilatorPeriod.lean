import Mathlib.LinearAlgebra.AnnihilatingPolynomial

/-! A displayed annihilating polynomial on one selected vector implies
its period whenever that polynomial divides X^n-1. This uses only the
actual endomorphism and the displayed polynomial identity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LinearMapSelectedAnnihilatorPeriod
open Polynomial
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem pow_apply_eq (A : Module.End R V) (n : ℕ) (f : R[X]) (v : V)
    (hf : f ∣ (X^n-1 : R[X])) (hv : (aeval A f) v = 0) : (A^n) v = v := by
  obtain ⟨q,hq⟩ := hf
  have hq' : (X^n-1 : R[X]) = q*f := hq.trans (mul_comm f q)
  have hz : (aeval A (X^n-1 : R[X])) v = 0 := by
    rw [hq',map_mul,Module.End.mul_apply,hv,map_zero]
  have hsub : (A^n) v-v = 0 := by
    simpa only [map_sub,map_pow,aeval_X,map_one,
      LinearMap.sub_apply,Module.End.one_apply] using hz
  exact sub_eq_zero.mp hsub

end SymmetricSubgroupAsymptotics.LinearMapSelectedAnnihilatorPeriod
