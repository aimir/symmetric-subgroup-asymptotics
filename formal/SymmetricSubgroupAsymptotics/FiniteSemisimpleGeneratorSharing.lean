import SymmetricSubgroupAsymptotics.FiniteSemisimpleScalarProjection
import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators

/-! Fully invariant summands of a finite semisimple module share generator
slots. Actual scalar projections isolate each component of the packed
tuple, so no unjustified projection-stability assertion is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

theorem moduleGeneratedBy_fullyInvariant_decomposition
    {R M I : Type} [Ring R] [AddCommGroup M] [Module R M] [Finite M]
    [IsSemisimpleModule R M] [Fintype I]
    (P Q : I → Submodule R M)
    (hcomp : ∀ i, IsCompl (P i) (Q i))
    (hP : ∀ i, (P i).IsFullyInvariant) (hQ : ∀ i, (Q i).IsFullyInvariant)
    (hother : ∀ i j, j≠i → P j≤Q i) (htop : (⨆ i, P i)=⊤)
    (t : ℕ) (hgen : ∀ i, ModuleGeneratedBy R (P i) t) :
    ModuleGeneratedBy R M t := by
  choose v hv using hgen
  let x : Fin t → M := fun j => ∑ i : I, (v i j : M)
  let U : Submodule R M := Submodule.span R (Set.range x)
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
  refine ⟨x,top_unique ?_⟩
  rw [←htop]
  exact iSup_le hle

end SymmetricSubgroupAsymptotics
