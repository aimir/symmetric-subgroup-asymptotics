import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators

/-! Two complementary types share the SAME generator positions when an
actual ring operator projects onto one and kills the other. This packs
actual tuples and does not sum their separate capacities. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ComplementaryProjectorGeneratorPacking

theorem generatedBy {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (S T : Submodule R M) (e : R)
    (heS : ∀ s : S, e • (s : M)=(s : M))
    (heT : ∀ t : T, e • (t : M)=0) (hsup : S⊔T=⊤)
    {n : ℕ} (hS : ModuleGeneratedBy R S n) (hT : ModuleGeneratedBy R T n) :
    ModuleGeneratedBy R M n := by
  obtain ⟨u,hu⟩ := hS
  obtain ⟨v,hv⟩ := hT
  let w : Fin n → M := fun i => (u i : M)+(v i : M)
  let P := Submodule.span R (Set.range w)
  have hw : ∀ i, w i∈P := fun i => Submodule.subset_span ⟨i,rfl⟩
  have hum : ∀ i, (u i : M)∈P := by
    intro i
    have h := P.smul_mem e (hw i)
    simpa only [w,smul_add,heS,heT,add_zero] using h
  have hvm : ∀ i, (v i : M)∈P := by
    intro i
    have h := P.sub_mem (hw i) (hum i)
    simpa only [w,add_sub_cancel_left] using h
  have hSP : S≤P := by
    have h : Submodule.span R (Set.range u)≤P.comap S.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hum i
    rw [hu] at h
    intro x hx
    exact h (show (⟨x,hx⟩ : S)∈(⊤ : Submodule R S) from trivial)
  have hTP : T≤P := by
    have h : Submodule.span R (Set.range v)≤P.comap T.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hvm i
    rw [hv] at h
    intro x hx
    exact h (show (⟨x,hx⟩ : T)∈(⊤ : Submodule R T) from trivial)
  refine ⟨w,top_unique ?_⟩
  rw [← hsup]
  exact sup_le hSP hTP

end SymmetricSubgroupAsymptotics.ComplementaryProjectorGeneratorPacking
