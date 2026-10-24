import SymmetricSubgroupAsymptotics.LinearMapElementaryDivisorDecomposition
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Every finite-dimensional endomorphism has actual monic cyclic
polynomial quotient coordinates, with the total polynomial degree equal
to its dimension. Zero-dimensional factors are allowed at this stage. -/
set_option autoImplicit false
noncomputable section
open scoped DirectSum BigOperators
open Polynomial
namespace SymmetricSubgroupAsymptotics.LinearMapMonicCyclicDecomposition
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]

structure Chart (A : Module.End K V) where
  ι : Type u
  [fintype : Fintype ι]
  polynomial : ι → K[X]
  monic : ∀ i, (polynomial i).Monic
  equiv : Module.AEval' A ≃ₗ[K[X]]
    ⨁ i : ι, K[X] ⧸ Submodule.span K[X] ({polynomial i} : Set K[X])

attribute [instance] Chart.fintype

set_option backward.isDefEq.respectTransparency false in
theorem exists_chart (A : Module.End K V) : Nonempty (Chart A) := by
  classical
  let C := LinearMapElementaryDivisorDecomposition.chart A
  let p : C.ι → K[X] := fun i => normalize (C.polynomial i ^ C.exponent i)
  have hp (i : C.ι) : (p i).Monic :=
    Polynomial.monic_normalize (pow_ne_zero _ (C.irreducible i).ne_zero)
  have hspan (i : C.ι) :
      Submodule.span K[X] ({C.polynomial i ^ C.exponent i} : Set K[X]) =
        Submodule.span K[X] ({p i} : Set K[X]) :=
    Ideal.span_singleton_eq_span_singleton.mpr (associated_normalize _)
  exact ⟨⟨C.ι, p, hp, C.equiv.trans (DFinsupp.mapRange.linearEquiv
    (fun i => Submodule.quotEquivOfEq _ _ (hspan i)))⟩⟩

def chart (A : Module.End K V) : Chart A := Classical.choice (exists_chart A)

theorem Chart.degree_sum {A : Module.End K V} (C : Chart A) :
    (∑ i : C.ι, (C.polynomial i).natDegree) = Module.finrank K V := by
  letI (i : C.ι) : Module.Finite K
      (K[X] ⧸ Submodule.span K[X] ({C.polynomial i} : Set K[X])) :=
    (C.monic i).finite_quotient
  calc
    _ = Module.finrank K (⨁ i : C.ι,
        K[X] ⧸ Submodule.span K[X] ({C.polynomial i} : Set K[X])) := by
      rw [Module.finrank_directSum]
      simp_rw [finrank_quotient_span_eq_natDegree]
    _ = Module.finrank K (Module.AEval' A) := (C.equiv.restrictScalars K).finrank_eq.symm
    _ = Module.finrank K V := (Module.AEval'.of A).finrank_eq.symm

end SymmetricSubgroupAsymptotics.LinearMapMonicCyclicDecomposition
