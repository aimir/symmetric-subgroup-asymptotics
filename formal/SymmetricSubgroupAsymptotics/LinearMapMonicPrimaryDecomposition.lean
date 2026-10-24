import SymmetricSubgroupAsymptotics.LinearMapElementaryDivisorDecomposition
import Mathlib.Algebra.Polynomial.FieldDivision

/-! The actual polynomial module of a finite-dimensional operator has
a finite decomposition into monic irreducible prime-power cyclic
summands. Associated generators give actual quotient equivalences.
This is existence of a code; no uniqueness or class-count bound is
assumed. Zero exponents are retained at this stage. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical DirectSum

namespace SymmetricSubgroupAsymptotics.LinearMapMonicPrimaryDecomposition
open Polynomial
universe u v
variable {K : Type u} [Field K]

def normalizedPowerQuotientEquiv (p : K[X]) (n : ℕ) :
    (K[X] ⧸ K[X] ∙ p^n) ≃ₗ[K[X]] (K[X] ⧸ K[X] ∙ (normalize p)^n) :=
  Submodule.quotEquivOfEq _ _
    (Ideal.span_singleton_eq_span_singleton.mpr
      (Associated.pow_pow (n := n) (associated_normalize p)))

theorem exists_monic_primePower_decomposition
    {V : Type v} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (A : Module.End K V) :
    letI : Module K[X] (Module.AEval' A) :=
      Module.AEval.instModulePolynomial (R := K) (M := V) A
    ∃ (ι : Type u) (_ : Fintype ι) (p : ι → K[X])
      (_ : ∀ i, Irreducible (p i) ∧ (p i).Monic) (e : ι → ℕ),
      Nonempty ((Module.AEval' A) ≃ₗ[K[X]]
        ⨁ i : ι, K[X] ⧸ K[X] ∙ (p i)^(e i)) := by
  letI : Module K[X] (Module.AEval' A) :=
    Module.AEval.instModulePolynomial (R := K) (M := V) A
  let C := LinearMapElementaryDivisorDecomposition.chart A
  refine ⟨C.ι,inferInstance,(fun i => normalize (C.polynomial i)),?_,C.exponent,?_⟩
  · intro i
    exact ⟨Associated.irreducible (associated_normalize (C.polynomial i)) (C.irreducible i),
      Polynomial.monic_normalize (C.irreducible i).ne_zero⟩
  · exact ⟨C.equiv.trans (DFinsupp.mapRange.linearEquiv
      (fun i => normalizedPowerQuotientEquiv (C.polynomial i) (C.exponent i)))⟩

end SymmetricSubgroupAsymptotics.LinearMapMonicPrimaryDecomposition
