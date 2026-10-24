import SymmetricSubgroupAsymptotics.LinearMapMaximalAnnihilatorVector
import Mathlib.RingTheory.PowerBasis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual cyclic bases when the degree of the minimal polynomial equals
the dimension. The selected vector comes from its polynomial annihilator,
so no cardinality or union-of-subspaces argument is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LinearMapCyclicPowerBasis

open Polynomial Module
open scoped BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]

omit [Module.Finite K V] in
theorem independent_powers (A : Module.End K V) (v : V)
    (hv : ∀ p : K[X], (aeval A p) v = 0 ↔ aeval A p = 0) :
    LinearIndependent K (fun i : Fin (minpoly K A).natDegree => (A ^ i.val) v) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let p : K[X] := ∑ i : Fin (minpoly K A).natDegree, C (c i) * X ^ i.val
  have hp : aeval A p = ∑ i : Fin (minpoly K A).natDegree, c i • A ^ i.val := by
    simp only [p, map_sum, map_mul, aeval_C, aeval_X_pow, Algebra.smul_def]
  have hpv : (aeval A p) v = 0 := by
    rw [hp]
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using hc
  have hz := (hv p).mp hpv
  rw [hp] at hz
  exact Fintype.linearIndependent_iff.mp (linearIndependent_pow A) c hz

theorem exists_independent_powers (A : Module.End K V) :
    ∃ v : V,
      LinearIndependent K (fun i : Fin (minpoly K A).natDegree => (A ^ i.val) v) := by
  obtain ⟨v, hv⟩ := LinearMapMaximalAnnihilatorVector.exists_vector A
  exact ⟨v, independent_powers A v hv⟩

theorem exists_basis (A : Module.End K V)
    (hd : (minpoly K A).natDegree = Module.finrank K V) :
    ∃ (v : V) (b : Basis (Fin (minpoly K A).natDegree) K V),
      ∀ i, b i = (A ^ i.val) v := by
  obtain ⟨v, hv⟩ := exists_independent_powers A
  let b := basisOfLinearIndependentOfCardEqFinrank'
    (fun i : Fin (minpoly K A).natDegree => (A ^ i.val) v) hv
    (by simpa only [Fintype.card_fin] using hd)
  refine ⟨v, b, ?_⟩
  intro i
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) i

theorem exists_basis_three (A : Module.End K V)
    (hd : Module.finrank K V = 3) (hmin : (minpoly K A).natDegree = 3) :
    ∃ (v : V) (b : Basis (Fin 3) K V), ∀ i, b i = (A ^ i.val) v := by
  obtain ⟨v, hv⟩ := exists_independent_powers A
  have hi : LinearIndependent K (fun i : Fin 3 => (A ^ i.val) v) := by
    exact hv.comp (Fin.cast hmin.symm) (Fin.cast_injective hmin.symm)
  let b := basisOfLinearIndependentOfCardEqFinrank'
    (fun i : Fin 3 => (A ^ i.val) v) hi
    (by simpa only [Fintype.card_fin] using hd.symm)
  refine ⟨v, b, ?_⟩
  intro i
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) i

end SymmetricSubgroupAsymptotics.LinearMapCyclicPowerBasis
