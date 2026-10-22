import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootedCliques

/-! Relation equivalences transport maximal cliques, with original
vertex sets rather than classes of twins. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootedCliques
variable {X Y : Type*} (R : X → X → Prop) (Q : Y → Y → Prop)
variable (e : X ≃ Y) (he : ∀ a b, Q (e a) (e b) ↔ R a b)

include he in
theorem clique_preimage_iff (T : Set Y) : Clique R (e ⁻¹' T) ↔ Clique Q T := by
  constructor
  · intro h a ha b hb
    have hha : e.symm a ∈ e ⁻¹' T := by simpa only [Set.mem_preimage, e.apply_symm_apply] using ha
    have hhb : e.symm b ∈ e ⁻¹' T := by simpa only [Set.mem_preimage, e.apply_symm_apply] using hb
    rcases h (e.symm a) hha (e.symm b) hhb with hh | hr
    · exact Or.inl (by simpa only [e.apply_symm_apply] using congrArg e hh)
    · exact Or.inr (by simpa only [e.apply_symm_apply] using (he _ _).mpr hr)
  · intro h a ha b hb
    rcases h (e a) ha (e b) hb with hh | hr
    · exact Or.inl (e.injective hh)
    · exact Or.inr ((he a b).mp hr)

include he in
theorem maximal_clique_preimage_iff (T : Set Y) :
    MaximalClique R (e ⁻¹' T) ↔ MaximalClique Q T := by
  constructor
  · intro h
    refine ⟨(clique_preimage_iff R Q e he T).mp h.1, ?_⟩
    intro U hU hTU y hy
    have hpre := h.2 (e ⁻¹' U) ((clique_preimage_iff R Q e he U).mpr hU)
      (fun _ hx => hTU hx)
    have hy' : e.symm y ∈ e ⁻¹' U := by simpa only [Set.mem_preimage, e.apply_symm_apply] using hy
    simpa only [Set.mem_preimage, e.apply_symm_apply] using hpre hy'
  · intro h
    refine ⟨(clique_preimage_iff R Q e he T).mpr h.1, ?_⟩
    intro U hU hTU x hx
    have him : Clique Q (e '' U) := by
      rintro a ⟨u, hu, rfl⟩ b ⟨v, hv, rfl⟩
      rcases hU u hu v hv with hh | hr
      · exact Or.inl (congrArg e hh)
      · exact Or.inr ((he u v).mpr hr)
    have hsub : T ⊆ e '' U := by
      intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply hTU
      simpa only [Set.mem_preimage, e.apply_symm_apply] using hy
    exact h.2 (e '' U) him hsub ⟨x, hx, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootedCliques
