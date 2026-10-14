import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators
import SymmetricSubgroupAsymptotics.PidSubmoduleGeneratorBound
import Mathlib.Algebra.Algebra.Tower

/-!
# Uniform cyclicity from actual matrix units

Suppose acting scalars realize the row matrix units on a rectangular
coordinate space with at least as many rows as columns. Every invariant
submodule is cyclic: choose a basis of its first-row fibre, put its basis
vectors in different rows, and recover all rows with the matrix units.

The other acting scalars need not preserve any chosen column. In
particular, no semisimplicity or classification of invariant submodules is
assumed, and the theorem controls submodules rather than only the ambient
module.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics
namespace ModuleGeneratedBy

variable {k R M : Type} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

/-- Actual row matrix units make every submodule cyclic when the number
of columns does not exceed the number of rows. -/
theorem one_of_matrixUnits {n m : ℕ} [NeZero n] (hmn : m ≤ n)
    (e : M ≃ₗ[k] (Fin n → Fin m → k))
    (a : Fin n → Fin n → R)
    (ha : ∀ i j x, e (a i j • x) = Pi.single i (e x j))
    (W : Submodule R M) : ModuleGeneratedBy R W 1 := by
  let pr : M →ₗ[k] (Fin m → k) := (LinearMap.proj (0 : Fin n)).comp e.toLinearMap
  let U : Submodule k (Fin m → k) := (W.restrictScalars k).map pr
  have hrow {x : M} (hx : x ∈ W) (i : Fin n) : e x i ∈ U := by
    refine ⟨a 0 i • x, W.smul_mem _ hx, ?_⟩
    change e (a 0 i • x) 0 = e x i
    rw [ha]
    simp
  have hsingle (i : Fin n) (u : U) : e.symm (Pi.single i (u : Fin m → k)) ∈ W := by
    obtain ⟨x, hx, hxu⟩ := u.property
    have heq : e.symm (Pi.single i (u : Fin m → k)) = a i 0 • x := by
      apply e.injective
      rw [e.apply_symm_apply, ha]
      exact congrArg (Pi.single i) hxu.symm
    rw [heq]
    exact W.smul_mem _ hx
  obtain ⟨d, snf⟩ := Submodule.smithNormalForm (Pi.basisFun k (Fin m)) U
  let b : Module.Basis (Fin d) k U := snf.bN
  let j : Fin d ↪ Fin n := snf.f.trans
    ⟨Fin.castLE hmn, Fin.castLE_injective hmn⟩
  let w : M := ∑ t : Fin d, e.symm (Pi.single (j t) (b t : Fin m → k))
  have hw : w ∈ W := W.sum_mem (fun t _ ↦ hsingle (j t) (b t))
  have hwrow (t : Fin d) : e w (j t) = (b t : Fin m → k) := by
    simp only [w, map_sum, e.apply_symm_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single t]
    · simp
    · intro t' _ hne
      have hj : j t' ≠ j t := fun h ↦ hne (j.injective h)
      simp [Pi.single_apply, hj, Ne.symm hj]
    · intro hnot
      exact (hnot (Finset.mem_univ t)).elim
  let v : Fin 1 → W := fun _ ↦ ⟨w, hw⟩
  let N : Submodule R W := Submodule.span R (Set.range v)
  let P : Submodule R M := N.map W.subtype
  have hwP : w ∈ P := by
    refine ⟨v 0, Submodule.subset_span (Set.mem_range_self (0 : Fin 1)), rfl⟩
  have hbP (i : Fin n) (t : Fin d) :
      e.symm (Pi.single i (b t : Fin m → k)) ∈ P := by
    have h := P.smul_mem (a i (j t)) hwP
    have heq : a i (j t) • w = e.symm (Pi.single i (b t : Fin m → k)) := by
      apply e.injective
      rw [ha, hwrow, e.apply_symm_apply]
    exact heq ▸ h
  have hrowP (i : Fin n) (u : U) :
      e.symm (Pi.single i (u : Fin m → k)) ∈ P := by
    let f : U →ₗ[k] M :=
      e.symm.toLinearMap.comp ((LinearMap.single k (fun _ : Fin n ↦ Fin m → k) i).comp U.subtype)
    have hsum := congrArg f (b.sum_repr u)
    simp only [map_sum, map_smul] at hsum
    change f u ∈ P
    rw [← hsum]
    apply P.sum_mem
    intro t _
    exact (P.restrictScalars k).smul_mem _ (hbP i t)
  have hWP : W ≤ P := by
    intro x hx
    have hsum : (∑ i : Fin n, e.symm (Pi.single i (e x i))) = x := by
      rw [← map_sum, LinearMap.sum_single_apply (fun _ : Fin n ↦ Fin m → k),
        e.symm_apply_apply]
    rw [← hsum]
    exact P.sum_mem (fun i _ ↦ hrowP i ⟨e x i, hrow hx i⟩)
  refine ⟨v, top_unique ?_⟩
  intro x _
  obtain ⟨y, hy, hxy⟩ := hWP x.property
  have : y = x := Subtype.ext hxy
  exact this ▸ hy

end ModuleGeneratedBy
end SymmetricSubgroupAsymptotics

end
