import SymmetricSubgroupAsymptotics.CFSGTwistedASLTwoDerivedWitness

/-! The rank-two twisted case needs noncommutation, not a nonscalar
2-by-2 commutator. This weaker exact matrix fact includes the fixed field
of order three, whose SL2 derived subgroup is still nonabelian. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedASLTwoDerivedWitness
variable {K : Type} [Field K]

theorem deltaUnit_not_commute (a : K) (ha : a ≠ 0) (haone : a ≠ 1) :
    ¬ Commute (deltaUnit (1 : K)) (deltaUnit a) := by
  intro h
  have he := congrArg (fun w : (Matrix (Fin 2) (Fin 2) K)ˣ =>
    (w : Matrix (Fin 2) (Fin 2) K)) h.eq
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) he
  change ((deltaUnit (1 : K) : Matrix (Fin 2) (Fin 2) K) *
      (deltaUnit a : Matrix (Fin 2) (Fin 2) K)) 1 1 =
    ((deltaUnit a : Matrix (Fin 2) (Fin 2) K) *
      (deltaUnit (1 : K) : Matrix (Fin 2) (Fin 2) K)) 1 1 at h11
  simp only [deltaUnit_val, Matrix.mul_apply, Fin.sum_univ_two,
    deltaArray, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at h11
  apply haone
  apply mul_left_cancel₀ ha
  linear_combination -h11

theorem deltaUnit_commutator_ne_one (a : K) (ha : a ≠ 0) (haone : a ≠ 1) :
    ⁅deltaUnit (1 : K), deltaUnit a⁆ ≠ 1 := by
  intro h
  apply deltaUnit_not_commute a ha haone
  exact commutatorElement_eq_one_iff_mul_comm.mp h

end SymmetricSubgroupAsymptotics.CFSGTwistedASLTwoDerivedWitness
