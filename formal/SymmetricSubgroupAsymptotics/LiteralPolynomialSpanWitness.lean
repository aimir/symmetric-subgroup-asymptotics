import SymmetricSubgroupAsymptotics.RepresentationAlgebraPolynomialGeneratorBound
import Mathlib.LinearAlgebra.Pi

/-!
# A finite recurrence certificate for polynomial spanning

The displayed vectors form short operator recurrences. A literal inverse
matrix reconstructs every coordinate vector from selected recurrence
entries. These equalities certify polynomial spanning without a rank
oracle or enumeration of vectors or invariant subspaces.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Polynomial MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics

structure LiteralPolynomialSpanWitness {k : Type} [Field k] {d : ℕ}
    (T : Module.End k (Fin d → k)) (r h : ℕ) where
  vectors : Fin r → Fin (h + 1) → Fin d → k
  step : ∀ (j : Fin r) (m : Fin h), vectors j m.succ = T (vectors j m.castSucc)
  selected : Fin d → Fin r × Fin (h + 1)
  coefficient : Fin d → Fin d → k
  point_eq : ∀ i x, (∑ j, coefficient i j *
    vectors (selected j).1 (selected j).2 x) = (Pi.single i 1 : Fin d → k) x

namespace LiteralPolynomialSpanWitness

variable {k : Type} [Field k] {d r h : ℕ}
  {T : Module.End k (Fin d → k)} (C : LiteralPolynomialSpanWitness T r h)

theorem polynomial_span :
    Submodule.span k[X]
      (Set.range (fun j ↦ Module.AEval'.of T (C.vectors j 0))) = ⊤ := by
  let e := Module.AEval'.of T
  let P : Submodule k[X] (Module.AEval' T) :=
    Submodule.span k[X] (Set.range (fun j ↦ e (C.vectors j 0)))
  have htable : ∀ j m, e (C.vectors j m) ∈ P := by
    intro j m
    refine Fin.induction ?_ ?_ m
    · exact Submodule.subset_span ⟨j, rfl⟩
    · intro i hi
      rw [C.step j i]
      have hx := P.smul_mem (Polynomial.X : k[X]) hi
      simpa only [e, Module.AEval'.X_smul_of] using hx
  have hdelta : ∀ i, e (Pi.single i (1 : k)) ∈ P := by
    intro i
    have heq : (∑ j, C.coefficient i j •
        C.vectors (C.selected j).1 (C.selected j).2) = (Pi.single i 1 : Fin d → k) := by
      funext x
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using C.point_eq i x
    have hm : e (∑ j, C.coefficient i j •
        C.vectors (C.selected j).1 (C.selected j).2) ∈ P := by
      rw [map_sum]
      apply P.sum_mem
      intro j _
      rw [map_smul]
      exact P.smul_of_tower_mem _ (htable _ _)
    rwa [heq] at hm
  have hall : ∀ v : Fin d → k, e v ∈ P := by
    intro v
    have hdecomp : (∑ i, v i • (Pi.single i 1 : Fin d → k)) = v := by
      calc
        (∑ i, v i • (Pi.single i 1 : Fin d → k)) = ∑ i, Pi.single i (v i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Pi.single_smul]
          simp
        _ = v := LinearMap.sum_single_apply (fun _ : Fin d ↦ k) v
    have hp : (∑ i, v i • e (Pi.single i 1)) ∈ P :=
      P.sum_mem fun i _ ↦ P.smul_of_tower_mem (v i) (hdelta i)
    have heq : (∑ i, v i • e (Pi.single i 1)) = e v := by
      simpa only [map_sum, map_smul] using congrArg e hdecomp
    exact heq ▸ hp
  apply top_unique
  intro x _
  simpa only [LinearEquiv.apply_symm_apply] using hall (e.symm x)

include C in
/-- A recurrence and inverse-matrix certificate for a group-algebra
operator proves the uniform bound on the original representation. -/
theorem uniform {G : Type} [Group G]
    (rho : Representation k G (Fin d → k)) (a : k[G])
    (hT : T = rho.asAlgebraHom a) :
    UniformSubrepresentationGeneratorBound rho r := by
  subst T
  exact uniformSubrepresentationGeneratorBound_of_algebraPolynomial
    rho a _ C.polynomial_span

end LiteralPolynomialSpanWitness
end SymmetricSubgroupAsymptotics

end
