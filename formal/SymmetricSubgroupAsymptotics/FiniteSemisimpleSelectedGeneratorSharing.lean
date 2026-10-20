import SymmetricSubgroupAsymptotics.FiniteSemisimpleGeneratorSharing

/-! The same packed generator bound for a selected sum of fully invariant
summands. The containing module need not be exhausted by the selection. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

theorem moduleGeneratedBy_selected_fullyInvariant_sum
    {R M I : Type} [Ring R] [AddCommGroup M] [Module R M] [Finite M]
    [IsSemisimpleModule R M] [Fintype I]
    (P Q : I → Submodule R M)
    (hcomp : ∀ i, IsCompl (P i) (Q i))
    (hP : ∀ i, (P i).IsFullyInvariant) (hQ : ∀ i, (Q i).IsFullyInvariant)
    (hother : ∀ i j, j≠i → P j≤Q i)
    (t : ℕ) (hgen : ∀ i, ModuleGeneratedBy R (P i) t) :
    ModuleGeneratedBy R (↥(⨆ i, P i : Submodule R M)) t := by
  choose v hv using hgen
  let x : Fin t → M := fun j => ∑ i : I, (v i j : M)
  let U : Submodule R M := Submodule.span R (Set.range x)
  let L : Submodule R M := ⨆ i, P i
  have hcomponent (i : I) (j : Fin t) : (v i j : M)∈U := by
    obtain ⟨r,hrP,hrQ⟩ := scalar_projection_of_fullyInvariant_complement
      (P i) (Q i) (hcomp i) (hP i) (hQ i)
    have he : r • x j=(v i j : M) := by
      change r • (∑ q : I, (v q j : M))=(v i j : M)
      rw [Finset.smul_sum,Finset.sum_eq_single i]
      · exact hrP _ (v i j).property
      · intro q _ hqi
        exact hrQ _ (hother i q hqi (v q j).property)
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    rw [←he]
    exact U.smul_mem r (Submodule.subset_span (Set.mem_range_self j))
  have hle (i : I) : P i≤U := by
    intro m hm
    have hspan : Submodule.span R (Set.range (v i))≤U.comap (P i).subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact hcomponent i j
    have hmem : (⟨m,hm⟩ : P i)∈Submodule.span R (Set.range (v i)) := by
      rw [hv i]
      trivial
    exact hspan hmem
  have hUL : U≤L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact L.sum_mem (fun i _ => (le_iSup P i) (v i j).property)
  have heq : U=L := le_antisymm hUL (iSup_le hle)
  let y : Fin t → L := fun j => ⟨x j,hUL (Submodule.subset_span (Set.mem_range_self j))⟩
  refine ⟨y,?_⟩
  apply Submodule.map_injective_of_injective L.subtype_injective
  have hm : (Submodule.span R (Set.range y)).map L.subtype=U := by
    rw [Submodule.map_span,←Set.range_comp]
    rfl
  rw [hm,Submodule.map_top,L.range_subtype,heq]

end SymmetricSubgroupAsymptotics
