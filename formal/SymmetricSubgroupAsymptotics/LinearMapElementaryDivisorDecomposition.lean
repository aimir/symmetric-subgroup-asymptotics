import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.FiniteDimensional

/-! Actual finite-dimensional endomorphisms admit polynomial cyclic
quotient coordinates. This is the shared starting point for conjugacy
codes in arbitrary dimension; no canonical-form premise is supplied.
The elementary divisors here are not yet normalized or counted. -/
set_option autoImplicit false
noncomputable section
open scoped DirectSum
open Polynomial
namespace SymmetricSubgroupAsymptotics.LinearMapElementaryDivisorDecomposition
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]

structure Chart (A : Module.End K V) where
  ι : Type u
  [fintype : Fintype ι]
  polynomial : ι → K[X]
  irreducible : ∀ i, Irreducible (polynomial i)
  exponent : ι → ℕ
  equiv : Module.AEval' A ≃ₗ[K[X]]
    ⨁ i : ι, K[X] ⧸ Submodule.span K[X] ({polynomial i ^ exponent i} : Set K[X])

attribute [instance] Chart.fintype

set_option backward.isDefEq.respectTransparency false in
theorem exists_chart (A : Module.End K V) : Nonempty (Chart A) := by
  letI : Module K[X] (Module.AEval' A) :=
    Module.AEval.instModulePolynomial (R := K) (M := V) A
  obtain ⟨ι, fι, p, hp, e, ⟨E⟩⟩ := Module.equiv_directSum_of_isTorsion
    (R := K[X]) (M := Module.AEval' A)
    (Module.AEval.isTorsion_of_finiteDimensional K V A)
  exact ⟨⟨ι, p, hp, e, E⟩⟩

def chart (A : Module.End K V) : Chart A := Classical.choice (exists_chart A)

end SymmetricSubgroupAsymptotics.LinearMapElementaryDivisorDecomposition
