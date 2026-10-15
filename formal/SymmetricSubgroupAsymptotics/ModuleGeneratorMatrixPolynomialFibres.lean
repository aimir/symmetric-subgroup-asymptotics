import SymmetricSubgroupAsymptotics.ModuleGeneratorMatrixUnits
import SymmetricSubgroupAsymptotics.RepresentationPolynomialGeneratorBound

/-! Matrix rows can share polynomial generator positions. If actual
acting scalars realize all row matrix units, and another actual scalar
acts by the same operator on every row, an n-generated polynomial fibre
in n matrix rows makes every original submodule cyclic. The PID theorem
is applied to each actual first-row fibre, not just to the ambient space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators Polynomial

namespace SymmetricSubgroupAsymptotics
namespace ModuleGeneratedBy

variable {k R M V : Type} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
  [AddCommGroup V] [Module k V]

theorem one_of_matrixUnits_of_polynomial {n : ℕ} [NeZero n]
    (e : M ≃ₗ[k] (Fin n → V))
    (a : Fin n → Fin n → R)
    (ha : ∀ i j x, e (a i j • x) = Pi.single i (e x j))
    (b : R) (T : Module.End k V)
    (hb : ∀ x, e (b • x) = fun i ↦ T (e x i))
    (v : Fin n → Module.AEval' T)
    (hv : Submodule.span k[X] (Set.range v) = ⊤)
    (W : Submodule R M) : ModuleGeneratedBy R W 1 := by
  let pr : M →ₗ[k] V := (LinearMap.proj (0 : Fin n)).comp e.toLinearMap
  let U : Submodule k V := (W.restrictScalars k).map pr
  have hrow {x : M} (hx : x ∈ W) (i : Fin n) : e x i ∈ U := by
    refine ⟨a 0 i • x, W.smul_mem _ hx, ?_⟩
    change e (a 0 i • x) 0 = e x i
    rw [ha]
    simp
  have hsingle (i : Fin n) (u : U) : e.symm (Pi.single i (u : V)) ∈ W := by
    obtain ⟨x, hx, hxu⟩ := u.property
    have heq : e.symm (Pi.single i (u : V)) = a i 0 • x := by
      apply e.injective
      rw [e.apply_symm_apply, ha]
      exact congrArg (Pi.single i) hxu.symm
    rw [heq]
    exact W.smul_mem _ hx
  have hUT : ∀ u, u ∈ U → T u ∈ U := by
    intro u hu
    obtain ⟨x, hx, hxu⟩ := hu
    refine ⟨b • x, W.smul_mem b hx, ?_⟩
    change e (b • x) 0 = T u
    rw [hb]
    exact congrArg T hxu
  let PU := Module.AEval.mapSubmodule k V T ⟨U, hUT⟩
  obtain ⟨u, hu⟩ := submodule_generatedBy_of_pid v hv PU
  let value : Fin n → V := fun j ↦ (Module.AEval'.of T).symm (u j).1
  have hvalue (j : Fin n) : value j ∈ U :=
    (Module.AEval.mem_mapSubmodule_apply k V T).mp (u j).property
  let w : M := ∑ j : Fin n, e.symm (Pi.single j (value j))
  have hw : w ∈ W := W.sum_mem (fun j _ ↦ hsingle j ⟨value j, hvalue j⟩)
  have hwrow (j : Fin n) : e w j = value j := by
    simp only [w, map_sum, e.apply_symm_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hne
      exact Pi.single_eq_of_ne hne.symm _
    · intro hnot
      exact (hnot (Finset.mem_univ j)).elim
  let generator : Fin 1 → W := fun _ ↦ ⟨w, hw⟩
  let N : Submodule R W := Submodule.span R (Set.range generator)
  let P : Submodule R M := N.map W.subtype
  have hwP : w ∈ P :=
    ⟨generator 0, Submodule.subset_span (Set.mem_range_self (0 : Fin 1)), rfl⟩
  have hvalueP (i j : Fin n) : e.symm (Pi.single i (value j)) ∈ P := by
    have hm := P.smul_mem (a i j) hwP
    have heq : a i j • w = e.symm (Pi.single i (value j)) := by
      apply e.injective
      rw [ha, hwrow, e.apply_symm_apply]
    exact heq ▸ hm
  have hsingleT (i : Fin n) (z : V) :
      e.symm (Pi.single i (T z)) = b • e.symm (Pi.single i z) := by
    apply e.injective
    rw [e.apply_symm_apply, hb, e.apply_symm_apply]
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]
  have hrowP (i : Fin n) (z : U) : e.symm (Pi.single i (z : V)) ∈ P := by
    let embedding : V →ₗ[k] M := e.symm.toLinearMap.comp (LinearMap.single k (fun _ : Fin n ↦ V) i)
    let S : Submodule k V := (P.restrictScalars k).comap embedding
    have hST : ∀ y, y ∈ S → T y ∈ S := by
      intro y hy
      change e.symm (Pi.single i (T y)) ∈ P
      rw [hsingleT]
      exact P.smul_mem b hy
    let SA := Module.AEval.mapSubmodule k V T ⟨S, hST⟩
    let Q : Submodule k[X] PU := SA.comap PU.subtype
    have hle : Submodule.span k[X] (Set.range u) ≤ Q := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      apply (Module.AEval.mem_mapSubmodule_apply k V T).mpr
      exact hvalueP i j
    have hQ : Q = ⊤ := by
      rw [hu] at hle
      exact top_unique hle
    have hz : Module.AEval'.of T (z : V) ∈ PU :=
      (Module.AEval.mem_mapSubmodule_apply k V T).mpr z.property
    have hzQ : (⟨Module.AEval'.of T (z : V), hz⟩ : PU) ∈ Q := by
      rw [hQ]
      exact Submodule.mem_top
    exact (Module.AEval.mem_mapSubmodule_apply k V T).mp hzQ
  have hWP : W ≤ P := by
    intro x hx
    have hsum : (∑ i : Fin n, e.symm (Pi.single i (e x i))) = x := by
      rw [← map_sum, LinearMap.sum_single_apply (fun _ : Fin n ↦ V),
        e.symm_apply_apply]
    rw [← hsum]
    exact P.sum_mem (fun i _ ↦ hrowP i ⟨e x i, hrow hx i⟩)
  refine ⟨generator, top_unique ?_⟩
  intro x _
  obtain ⟨y, hy, hxy⟩ := hWP x.property
  exact (Subtype.ext hxy : y = x) ▸ hy

end ModuleGeneratedBy
end SymmetricSubgroupAsymptotics

end
