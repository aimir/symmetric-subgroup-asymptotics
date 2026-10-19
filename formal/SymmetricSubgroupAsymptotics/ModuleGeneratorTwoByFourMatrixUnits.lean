import SymmetricSubgroupAsymptotics.ModuleGeneratorMatrixUnits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ModuleGeneratedBy
variable {k R M : Type} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
theorem two_of_matrixUnits_two_by_four
    (e : M ≃ₗ[k] (Fin 2 → Fin 4 → k))
    (a : Fin 2 → Fin 2 → R)
    (ha : ∀ i j x, e (a i j • x) = Pi.single i (e x j))
    (W : Submodule R M) : ModuleGeneratedBy R W 2 := by
  let pr : M →ₗ[k] (Fin 4 → k) := (LinearMap.proj (0 : Fin 2)).comp e.toLinearMap
  let U : Submodule k (Fin 4 → k) := (W.restrictScalars k).map pr
  have hrow {x : M} (hx : x ∈ W) (i : Fin 2) : e x i ∈ U := by
    refine ⟨a 0 i • x, W.smul_mem _ hx, ?_⟩
    change e (a 0 i • x) 0 = e x i
    rw [ha]
    simp
  have hsingle (i : Fin 2) (u : U) : e.symm (Pi.single i (u : Fin 4 → k)) ∈ W := by
    obtain ⟨x, hx, hxu⟩ := u.property
    have heq : e.symm (Pi.single i (u : Fin 4 → k)) = a i 0 • x := by
      apply e.injective
      rw [e.apply_symm_apply, ha]
      exact congrArg (Pi.single i) hxu.symm
    rw [heq]
    exact W.smul_mem _ hx
  obtain ⟨d, snf⟩ := Submodule.smithNormalForm (Pi.basisFun k (Fin 4)) U
  let b : Module.Basis (Fin d) k U := snf.bN
  let pair : Fin 4 ≃ Fin 2 × Fin 2 := (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2*2)).symm
  let j : Fin d ↪ Fin 2 × Fin 2 := snf.f.trans pair.toEmbedding
  let w : Fin 2 → M := fun r => ∑ t : Fin d,
    if (j t).1=r then e.symm (Pi.single (j t).2 (b t : Fin 4 → k)) else 0
  have hw (r : Fin 2) : w r ∈ W := by
    apply W.sum_mem
    intro t _
    split_ifs
    · exact hsingle _ _
    · exact W.zero_mem
  have hwrow (t : Fin d) : e (w (j t).1) (j t).2=(b t : Fin 4 → k) := by
    simp only [w,map_sum,Finset.sum_apply]
    rw [Finset.sum_eq_single t]
    · simp
    · intro u _ hne
      by_cases hs : (j u).1=(j t).1
      · have hr : (j u).2≠(j t).2 := by
          intro h
          exact hne (j.injective (Prod.ext hs h))
        simp [hs,Pi.single_eq_of_ne hr.symm]
      · simp [hs]
    · intro hnot
      exact (hnot (Finset.mem_univ t)).elim
  let v : Fin 2 → W := fun i ↦ ⟨w i, hw i⟩
  let N : Submodule R W := Submodule.span R (Set.range v)
  let P : Submodule R M := N.map W.subtype
  have hwP (i : Fin 2) : w i ∈ P := by
    exact ⟨v i,Submodule.subset_span (Set.mem_range_self i),rfl⟩
  have hbP (i : Fin 2) (t : Fin d) :
      e.symm (Pi.single i (b t : Fin 4 → k)) ∈ P := by
    have h := P.smul_mem (a i (j t).2) (hwP (j t).1)
    have heq : a i (j t).2 • w (j t).1 = e.symm (Pi.single i (b t : Fin 4 → k)) := by
      apply e.injective
      rw [ha, hwrow, e.apply_symm_apply]
    exact heq ▸ h
  have hrowP (i : Fin 2) (u : U) :
      e.symm (Pi.single i (u : Fin 4 → k)) ∈ P := by
    let f : U →ₗ[k] M :=
      e.symm.toLinearMap.comp ((LinearMap.single k (fun _ : Fin 2 ↦ Fin 4 → k) i).comp U.subtype)
    have hsum := congrArg f (b.sum_repr u)
    simp only [map_sum, map_smul] at hsum
    change f u ∈ P
    rw [← hsum]
    apply P.sum_mem
    intro t _
    exact (P.restrictScalars k).smul_mem _ (hbP i t)
  have hWP : W ≤ P := by
    intro x hx
    have hsum : (∑ i : Fin 2, e.symm (Pi.single i (e x i))) = x := by
      rw [← map_sum, LinearMap.sum_single_apply (fun _ : Fin 2 ↦ Fin 4 → k),
        e.symm_apply_apply]
    rw [← hsum]
    exact P.sum_mem (fun i _ ↦ hrowP i ⟨e x i, hrow hx i⟩)
  refine ⟨v, top_unique ?_⟩
  intro x _
  obtain ⟨y, hy, hxy⟩ := hWP x.property
  have : y = x := Subtype.ext hxy
  exact this ▸ hy

end SymmetricSubgroupAsymptotics.ModuleGeneratedBy
