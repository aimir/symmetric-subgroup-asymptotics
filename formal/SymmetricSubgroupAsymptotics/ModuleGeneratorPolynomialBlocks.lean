import SymmetricSubgroupAsymptotics.RepresentationPolynomialGeneratorBound
import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators
import Mathlib.LinearAlgebra.Pi

/-! Independent polynomial coordinate blocks can share one generator.
The coordinate blocks need not be invariant under the whole acting ring:
actual acting scalars project onto them and implement their polynomial
operators. Each intersection of an actual submodule with a block is
therefore polynomial-stable. PID generators of these intersections can
be added and recovered by the actual coordinate projections. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators Polynomial

namespace SymmetricSubgroupAsymptotics.ModuleGeneratedBy

variable {k R M I : Type} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
  [Fintype I] [DecidableEq I]
  (V : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

theorem one_of_polynomial_blocks
    (e : M ≃ₗ[k] (∀ i, V i))
    (a b : I → R) (T : ∀ i, Module.End k (V i))
    (ha : ∀ i x, e (a i • x) = Pi.single i (e x i))
    (hb : ∀ i x, e (b i • x) i = T i (e x i))
    (v : ∀ i, Fin 1 → Module.AEval' (T i))
    (hv : ∀ i, Submodule.span k[X] (Set.range (v i)) = ⊤)
    (W : Submodule R M) : ModuleGeneratedBy R W 1 := by
  let pr (i : I) : M →ₗ[k] V i := (LinearMap.proj i).comp e.toLinearMap
  let U (i : I) : Submodule k (V i) := (W.restrictScalars k).map (pr i)
  have hrow {x : M} (hx : x ∈ W) (i : I) : e x i ∈ U i :=
    ⟨x, hx, rfl⟩
  have hsingle (i : I) (z : U i) : e.symm (Pi.single i (z : V i)) ∈ W := by
    obtain ⟨x, hx, hxz⟩ := z.property
    have heq : e.symm (Pi.single i (z : V i)) = a i • x := by
      apply e.injective
      rw [e.apply_symm_apply, ha]
      exact congrArg (fun y : V i ↦ (Pi.single i y : ∀ j, V j)) hxz.symm
    rw [heq]
    exact W.smul_mem _ hx
  have hUT (i : I) : ∀ z, z ∈ U i → T i z ∈ U i := by
    intro z hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨b i • x, W.smul_mem _ hx, ?_⟩
    change e (b i • x) i = T i z
    rw [hb]
    exact congrArg (T i) hxz
  let PU (i : I) := Module.AEval.mapSubmodule k (V i) (T i) ⟨U i, hUT i⟩
  have hgen (i : I) : ModuleGeneratedBy k[X] (PU i) 1 :=
    submodule_generatedBy_of_pid (v i) (hv i) (PU i)
  choose u hu using hgen
  let value (i : I) : V i := (Module.AEval'.of (T i)).symm (u i 0).1
  have hvalue (i : I) : value i ∈ U i :=
    (Module.AEval.mem_mapSubmodule_apply k (V i) (T i)).mp (u i 0).property
  let w : M := ∑ i, e.symm (Pi.single i (value i))
  have hw : w ∈ W := W.sum_mem fun i _ ↦ hsingle i ⟨value i, hvalue i⟩
  have hwrow (i : I) : e w i = value i := by
    simp only [w, map_sum, e.apply_symm_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      exact Pi.single_eq_of_ne hji.symm _
    · simp
  let generator : Fin 1 → W := fun _ ↦ ⟨w, hw⟩
  let N : Submodule R W := Submodule.span R (Set.range generator)
  let P : Submodule R M := N.map W.subtype
  have hwP : w ∈ P :=
    ⟨generator 0, Submodule.subset_span (Set.mem_range_self (0 : Fin 1)), rfl⟩
  have hvalueP (i : I) : e.symm (Pi.single i (value i)) ∈ P := by
    have hm := P.smul_mem (a i) hwP
    have heq : a i • w = e.symm (Pi.single i (value i)) := by
      apply e.injective
      rw [ha, hwrow, e.apply_symm_apply]
    exact heq ▸ hm
  have hsingleT (i : I) (z : V i) :
      e.symm (Pi.single i (T i z)) = a i • (b i • e.symm (Pi.single i z)) := by
    apply e.injective
    rw [e.apply_symm_apply, ha, hb, e.apply_symm_apply, Pi.single_eq_same]
  have hrowP (i : I) (z : U i) : e.symm (Pi.single i (z : V i)) ∈ P := by
    let embedding : V i →ₗ[k] M :=
      e.symm.toLinearMap.comp (LinearMap.single k V i)
    let S : Submodule k (V i) := (P.restrictScalars k).comap embedding
    have hST : ∀ y, y ∈ S → T i y ∈ S := by
      intro y hy
      change e.symm (Pi.single i (T i y)) ∈ P
      rw [hsingleT]
      exact P.smul_mem _ (P.smul_mem _ hy)
    let SA := Module.AEval.mapSubmodule k (V i) (T i) ⟨S, hST⟩
    let Q : Submodule k[X] (PU i) := SA.comap (PU i).subtype
    have hle : Submodule.span k[X] (Set.range (u i)) ≤ Q := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      apply (Module.AEval.mem_mapSubmodule_apply k (V i) (T i)).mpr
      exact hvalueP i
    have hQ : Q = ⊤ := by
      rw [hu i] at hle
      exact top_unique hle
    have hz : Module.AEval'.of (T i) (z : V i) ∈ PU i :=
      (Module.AEval.mem_mapSubmodule_apply k (V i) (T i)).mpr z.property
    have hzQ : (⟨Module.AEval'.of (T i) (z : V i), hz⟩ : PU i) ∈ Q := by
      rw [hQ]
      exact Submodule.mem_top
    exact (Module.AEval.mem_mapSubmodule_apply k (V i) (T i)).mp hzQ
  have hWP : W ≤ P := by
    intro x hx
    have hsum : (∑ i, e.symm (Pi.single i (e x i))) = x := by
      rw [← map_sum, LinearMap.sum_single_apply V, e.symm_apply_apply]
    rw [← hsum]
    exact P.sum_mem fun i _ ↦ hrowP i ⟨e x i, hrow hx i⟩
  refine ⟨generator, top_unique ?_⟩
  intro x _
  obtain ⟨y, hy, hxy⟩ := hWP x.property
  exact (Subtype.ext hxy : y = x) ▸ hy

end SymmetricSubgroupAsymptotics.ModuleGeneratedBy

end
