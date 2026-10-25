import SymmetricSubgroupAsymptotics.LinearMapSelectedAnnihilatorPeriod
import Mathlib.Algebra.Polynomial.BigOperators

/-! A finite consecutive vector certificate supplies an annihilator and
hence a period for the SAME endomorphism. No independence, dimension or
minimal-polynomial assertion is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LinearMapSelectedKrylovPeriod
open Polynomial
open scoped BigOperators
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem pow_apply_eq_vector (A : Module.End R V) (d : ℕ)
    (v : Fin (d+1) → V)
    (hstep : ∀ i : Fin d, A (v i.castSucc)=v i.succ) (i : Fin (d+1)) :
    (A^i.val) (v 0)=v i := by
  have h : ∀ j : ℕ, ∀ hj : j<d+1, (A^j) (v 0)=v ⟨j,hj⟩ := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      have hjd : j<d := by omega
      rw [pow_succ',Module.End.mul_apply,ih (by omega)]
      exact hstep ⟨j,hjd⟩
  exact h i.val i.isLt

theorem aeval_sum_apply_eq_zero (A : Module.End R V) (d : ℕ)
    (c : Fin (d+1) → R) (v : Fin (d+1) → V)
    (hstep : ∀ i : Fin d, A (v i.castSucc)=v i.succ)
    (hrel : ∑ i : Fin (d+1), c i • v i=0) :
    (aeval A (∑ i : Fin (d+1), monomial i.val (c i))) (v 0)=0 := by
  classical
  rw [map_sum]
  calc
    (∑ i : Fin (d+1), aeval A (monomial i.val (c i))) (v 0)=
        ∑ i : Fin (d+1), (aeval A (monomial i.val (c i))) (v 0) := by
      simp only [LinearMap.sum_apply]
    _ = ∑ i : Fin (d+1), c i • v i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [aeval_monomial,Module.End.mul_apply,Module.algebraMap_end_apply,
        pow_apply_eq_vector A d v hstep i]
    _ = 0 := hrel

theorem pow_apply_eq (A : Module.End R V) (d n : ℕ)
    (c : Fin (d+1) → R) (v : Fin (d+1) → V)
    (hstep : ∀ i : Fin d, A (v i.castSucc)=v i.succ)
    (hrel : ∑ i : Fin (d+1), c i • v i=0)
    (hdiv : (∑ i : Fin (d+1), monomial i.val (c i)) ∣ (X^n-1 : R[X])) :
    (A^n) (v 0)=v 0 :=
  LinearMapSelectedAnnihilatorPeriod.pow_apply_eq A n _ _ hdiv
    (aeval_sum_apply_eq_zero A d c v hstep hrel)

end SymmetricSubgroupAsymptotics.LinearMapSelectedKrylovPeriod
