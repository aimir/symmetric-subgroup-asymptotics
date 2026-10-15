import SymmetricSubgroupAsymptotics.SeparatedNormalAxesQuotientSocles

/-! A pair of separated minimal normal subgroups suffices when every
nontrivial normal contains at least one of them. Each proper quotient then
factors through one of two actual maps, while the original socle has one
normal generator. This applies without a normal-chain assumption. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.TwoMinimalNormalQuotientSocles

variable {G : Type} [Group G]

theorem socle_eq_sup
    (A B : Subgroup G) (hA : IsMinimalNormalSubgroup A)
    (hB : IsMinimalNormalSubgroup B)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → A ≤ N ∨ B ≤ N) :
    finiteGroupSocle G = A ⊔ B := by
  letI := hA.1
  letI := hB.1
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x ⟨N,hN,hx⟩
    rcases hcover N hN.1 hN.2.1 with ha | hb
    · have he : A = N := hN.2.2 A hA.1 hA.2.1 ha
      exact Subgroup.mem_sup_left (he.symm ▸ hx)
    · have he : B = N := hN.2.2 B hB.1 hB.2.1 hb
      exact Subgroup.mem_sup_right (he.symm ▸ hx)
  · apply sup_le
    · intro x hx
      exact Subgroup.subset_normalClosure ⟨A,hA,hx⟩
    · intro x hx
      exact Subgroup.subset_normalClosure ⟨B,hB,hx⟩

theorem socle_one [Finite G]
    (A B : Subgroup G) (hA : IsMinimalNormalSubgroup A)
    (hB : IsMinimalNormalSubgroup B)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → A ≤ N ∨ B ≤ N)
    (hsep : NoCommonNormalQuotient A B) : SocleNormalGeneratorBound G 1 := by
  letI := hA.1
  letI := hB.1
  apply (socleNormalGeneratorBound_iff_normalGen_le _ _).mpr
  rw [socle_eq_sup A B hA hB hcover]
  exact (normalGen_sup_le_max_of_noCommonNormalQuotient A B hsep).trans
    (max_le (SeparatedNormalAxesQuotientSocles.normalGen_le_one_of_minimal A hA)
      (SeparatedNormalAxesQuotientSocles.normalGen_le_one_of_minimal B hB))

theorem socle_of_surjective [Finite G]
    {P Q : Type} [Group P] [Group Q]
    (p : G →* P) (hp : Function.Surjective p)
    (q : G →* Q) (hq : Function.Surjective q)
    (hA : IsMinimalNormalSubgroup p.ker) (hB : IsMinimalNormalSubgroup q.ker)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → p.ker ≤ N ∨ q.ker ≤ N)
    (hsep : NoCommonNormalQuotient p.ker q.ker)
    {t : ℕ} (ht : 1 ≤ t)
    (hP : ∀ N : Subgroup P, ∀ _ : N.Normal, SocleNormalGeneratorBound (P ⧸ N) t)
    (hQ : ∀ N : Subgroup Q, ∀ _ : N.Normal, SocleNormalGeneratorBound (Q ⧸ N) t)
    {X : Type} [Group X] (rho : G →* X) (hrho : Function.Surjective rho) :
    SocleNormalGeneratorBound X t := by
  by_cases hb : rho.ker = ⊥
  · exact CyclicSocleQuotientTools.socleBound_equiv
      (MulEquiv.ofBijective rho ⟨(MonoidHom.ker_eq_bot_iff rho).mp hb,hrho⟩)
      ((socle_one p.ker q.ker hA hB hcover hsep).mono ht)
  · rcases hcover rho.ker inferInstance hb with ha | hb
    · obtain ⟨f,hf,_⟩ := CyclicSocleQuotientTools.exists_surjective_factor p hp rho hrho ha
      exact CyclicSocleQuotientTools.socleBound_equiv
        (QuotientGroup.quotientKerEquivOfSurjective f hf) (hP f.ker inferInstance)
    · obtain ⟨f,hf,_⟩ := CyclicSocleQuotientTools.exists_surjective_factor q hq rho hrho hb
      exact CyclicSocleQuotientTools.socleBound_equiv
        (QuotientGroup.quotientKerEquivOfSurjective f hf) (hQ f.ker inferInstance)

end SymmetricSubgroupAsymptotics.TwoMinimalNormalQuotientSocles

end
