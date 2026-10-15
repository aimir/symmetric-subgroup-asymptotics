import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness

/-! An actual group-algebra operator that successively visits a permuted
coordinate basis makes every invariant subspace cyclic. Only the displayed
basis recurrence is needed; the operator need not be a group element. -/

set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics

def algebraPointCycleWitness {k : Type} [Field k] {d : ℕ}
    (T : Module.End k (Fin (d + 1) → k)) (p : Equiv.Perm (Fin (d + 1)))
    (hstep : ∀ m : Fin d,
      T (Pi.single (p m.castSucc) 1) = Pi.single (p m.succ) 1) :
    LiteralPolynomialSpanWitness T 1 d where
  vectors _ m := Pi.single (p m) 1
  step _ m := (hstep m).symm
  selected m := (0, m)
  coefficient i j := if p j = i then 1 else 0
  point_eq i x := by
    rw [Finset.sum_eq_single (p.symm i)]
    · change (if p (p.symm i) = i then (1 : k) else 0) *
        (Pi.single (p (p.symm i)) 1 : Fin (d + 1) → k) x =
          (Pi.single i 1 : Fin (d + 1) → k) x
      rw [if_pos (p.apply_symm_apply i), one_mul]
      exact congrArg (fun z ↦ (Pi.single z 1 : Fin (d + 1) → k) x)
        (p.apply_symm_apply i)
    · intro j _ hj
      have hji : p j ≠ i := by
        intro h
        apply hj
        have he := congrArg p.symm h
        simpa only [p.symm_apply_apply] using he
      simp only [if_neg hji, zero_mul]
    · simp

/-- Polynomial submodule theory upgrades this ambient coordinate cycle to
a uniform bound on every actual subrepresentation. -/
theorem uniformSubrepresentationGeneratorBound_of_algebra_pointCycle
    {k G : Type} [Field k] [Group G] {d : ℕ}
    (rho : Representation k G (Fin (d + 1) → k)) (a : k[G])
    (T : Module.End k (Fin (d + 1) → k)) (hT : T = rho.asAlgebraHom a)
    (p : Equiv.Perm (Fin (d + 1)))
    (hstep : ∀ m : Fin d,
      T (Pi.single (p m.castSucc) 1) = Pi.single (p m.succ) 1) :
    UniformSubrepresentationGeneratorBound rho 1 :=
  (algebraPointCycleWitness T p hstep).uniform rho a hT

end SymmetricSubgroupAsymptotics

end
