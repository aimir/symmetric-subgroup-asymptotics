import SymmetricSubgroupAsymptotics.ModuleGeneratorMatrixPolynomialFibres
import Mathlib.LinearAlgebra.Pi

/-! Independent matrix blocks can share one generator. Within block i,
actual acting scalars realize all matrix units on n i rows, and a further
scalar realizes the same polynomial operator on every row. If its fibre
has n i polynomial generators, PID generators of each actual submodule
can be packed into those rows. Projections recover each block separately.
No invariance of a coordinate block under the entire ring is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators Polynomial

namespace SymmetricSubgroupAsymptotics.ModuleGeneratedBy

variable {k R M I : Type} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
  [Fintype I] [DecidableEq I]
  (n : I → ℕ) [∀ i, NeZero (n i)]
  (V : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

theorem one_of_polynomial_matrix_blocks
    (e : M ≃ₗ[k] (∀ i, Fin (n i) → V i))
    (a : ∀ i, Fin (n i) → Fin (n i) → R)
    (b : I → R) (T : ∀ i, Module.End k (V i))
    (ha : ∀ i r s x,
      e (a i r s • x) = Pi.single i (Pi.single r (e x i s)))
    (hb : ∀ i r x, e (b i • x) i r = T i (e x i r))
    (v : ∀ i, Fin (n i) → Module.AEval' (T i))
    (hv : ∀ i, Submodule.span k[X] (Set.range (v i)) = ⊤)
    (W : Submodule R M) : ModuleGeneratedBy R W 1 := by
  let pr (i : I) : M →ₗ[k] V i :=
    (LinearMap.proj (0 : Fin (n i))).comp ((LinearMap.proj i).comp e.toLinearMap)
  let U (i : I) : Submodule k (V i) := (W.restrictScalars k).map (pr i)
  have hrow {x : M} (hx : x ∈ W) (i : I) (r : Fin (n i)) : e x i r ∈ U i := by
    refine ⟨a i 0 r • x, W.smul_mem _ hx, ?_⟩
    change e (a i 0 r • x) i 0 = e x i r
    rw [ha]
    simp
  have hsingle (i : I) (r : Fin (n i)) (z : U i) :
      e.symm (Pi.single i (Pi.single r (z : V i))) ∈ W := by
    obtain ⟨x, hx, hxz⟩ := z.property
    have heq : e.symm (Pi.single i (Pi.single r (z : V i))) = a i r 0 • x := by
      apply e.injective
      rw [e.apply_symm_apply, ha]
      exact congrArg (fun y : V i ↦
        (Pi.single i (Pi.single r y) : ∀ j, Fin (n j) → V j)) hxz.symm
    rw [heq]
    exact W.smul_mem _ hx
  have hUT (i : I) : ∀ z, z ∈ U i → T i z ∈ U i := by
    intro z hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨b i • x, W.smul_mem _ hx, ?_⟩
    change e (b i • x) i 0 = T i z
    rw [hb]
    exact congrArg (T i) hxz
  let PU (i : I) := Module.AEval.mapSubmodule k (V i) (T i) ⟨U i, hUT i⟩
  have hgen (i : I) : ModuleGeneratedBy k[X] (PU i) (n i) :=
    submodule_generatedBy_of_pid (v i) (hv i) (PU i)
  choose u hu using hgen
  let value (i : I) (r : Fin (n i)) : V i :=
    (Module.AEval'.of (T i)).symm (u i r).1
  have hvalue (i : I) (r : Fin (n i)) : value i r ∈ U i :=
    (Module.AEval.mem_mapSubmodule_apply k (V i) (T i)).mp (u i r).property
  let w : M := ∑ i, ∑ r : Fin (n i),
    e.symm (Pi.single i (Pi.single r (value i r)))
  have hw : w ∈ W := W.sum_mem fun i _ ↦
    W.sum_mem fun r _ ↦ hsingle i r ⟨value i r, hvalue i r⟩
  have hwrow (i : I) (r : Fin (n i)) : e w i r = value i r := by
    have he : e w = value := by
      simp only [w, map_sum, e.apply_symm_apply]
      have hinner (j : I) :
          (∑ s : Fin (n j),
            (Pi.single j (Pi.single s (value j s)) : ∀ i, Fin (n i) → V i)) =
            (Pi.single j (value j) : ∀ i, Fin (n i) → V i) := by
        have hs := congrArg (LinearMap.single k (fun i ↦ Fin (n i) → V i) j)
          (LinearMap.sum_single_apply (fun _ : Fin (n j) ↦ V j) (value j))
        simpa only [map_sum, LinearMap.single_apply] using hs
      simp_rw [hinner]
      exact LinearMap.sum_single_apply (fun i ↦ Fin (n i) → V i) value
    exact congrFun (congrFun he i) r
  let generator : Fin 1 → W := fun _ ↦ ⟨w, hw⟩
  let N : Submodule R W := Submodule.span R (Set.range generator)
  let P : Submodule R M := N.map W.subtype
  have hwP : w ∈ P :=
    ⟨generator 0, Submodule.subset_span (Set.mem_range_self (0 : Fin 1)), rfl⟩
  have hvalueP (i : I) (r s : Fin (n i)) :
      e.symm (Pi.single i (Pi.single r (value i s))) ∈ P := by
    have hm := P.smul_mem (a i r s) hwP
    have heq : a i r s • w = e.symm (Pi.single i (Pi.single r (value i s))) := by
      apply e.injective
      rw [ha, hwrow, e.apply_symm_apply]
    exact heq ▸ hm
  have hsingleT (i : I) (r : Fin (n i)) (z : V i) :
      e.symm (Pi.single i (Pi.single r (T i z))) =
        a i r r • (b i • e.symm (Pi.single i (Pi.single r z))) := by
    apply e.injective
    rw [e.apply_symm_apply, ha, hb, e.apply_symm_apply]
    simp
  have hrowP (i : I) (r : Fin (n i)) (z : U i) :
      e.symm (Pi.single i (Pi.single r (z : V i))) ∈ P := by
    let embedding : V i →ₗ[k] M := e.symm.toLinearMap.comp
      ((LinearMap.single k (fun j ↦ Fin (n j) → V j) i).comp
        (LinearMap.single k (fun _ : Fin (n i) ↦ V i) r))
    let S : Submodule k (V i) := (P.restrictScalars k).comap embedding
    have hST : ∀ y, y ∈ S → T i y ∈ S := by
      intro y hy
      change e.symm (Pi.single i (Pi.single r (T i y))) ∈ P
      rw [hsingleT]
      exact P.smul_mem _ (P.smul_mem _ hy)
    let SA := Module.AEval.mapSubmodule k (V i) (T i) ⟨S, hST⟩
    let Q : Submodule k[X] (PU i) := SA.comap (PU i).subtype
    have hle : Submodule.span k[X] (Set.range (u i)) ≤ Q := by
      apply Submodule.span_le.mpr
      rintro _ ⟨s, rfl⟩
      apply (Module.AEval.mem_mapSubmodule_apply k (V i) (T i)).mpr
      exact hvalueP i r s
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
    have hsum : (∑ i, ∑ r : Fin (n i),
        e.symm (Pi.single i (Pi.single r (e x i r)))) = x := by
      have hinner (i : I) :
          (∑ r : Fin (n i), e.symm (Pi.single i (Pi.single r (e x i r)))) =
            e.symm (Pi.single i (e x i)) := by
        rw [← map_sum]
        congr 1
        have hs := congrArg (LinearMap.single k (fun j ↦ Fin (n j) → V j) i)
          (LinearMap.sum_single_apply (fun _ : Fin (n i) ↦ V i) (e x i))
        simpa only [map_sum, LinearMap.single_apply] using hs
      simp_rw [hinner]
      rw [← map_sum, LinearMap.sum_single_apply (fun i ↦ Fin (n i) → V i),
        e.symm_apply_apply]
    rw [← hsum]
    exact P.sum_mem fun i _ ↦ P.sum_mem fun r _ ↦ hrowP i r ⟨e x i r, hrow hx i r⟩
  refine ⟨generator, top_unique ?_⟩
  intro x _
  obtain ⟨y, hy, hxy⟩ := hWP x.property
  exact (Subtype.ext hxy : y = x) ▸ hy

end SymmetricSubgroupAsymptotics.ModuleGeneratedBy

end
