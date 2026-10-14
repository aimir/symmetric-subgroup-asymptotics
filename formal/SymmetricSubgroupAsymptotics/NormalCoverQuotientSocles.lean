import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools
import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber

/-! Quotient-socle bounds lift across a literal nontrivial kernel which
lies in every nontrivial normal subgroup. The trivial denominator retains
the original group's normally cyclic socle. Every other denominator kills
the displayed kernel and factors through the original epimorphism.
No splitting, normal census, or all-normal-generator bound is required. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The all-quotient socle bound of the original target lifts unchanged
through a nontrivial normal-cover kernel, for every displayed epimorphism. -/
theorem quotientSocle_of_surjective_normal_cover
    {G Q R : Type} [Group G] [Group Q] [Group R]
    (π : G →* Q) (hπ : Function.Surjective π) (hker : π.ker ≠ ⊥)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → π.ker ≤ N)
    {t : ℕ} (ht : 1 ≤ t)
    (hQ : ∀ M : Subgroup Q, ∀ _ : M.Normal,
      SocleNormalGeneratorBound (Q ⧸ M) t)
    (ρ : G →* R) (hρ : Function.Surjective ρ) :
    SocleNormalGeneratorBound R t := by
  by_cases hbot : ρ.ker = ⊥
  · have hG : SocleNormalGeneratorBound G 1 :=
      CyclicSocleQuotientTools.socleBound_of_normal_cover π.ker hker hcover
    exact CyclicSocleQuotientTools.socleBound_equiv
      (MulEquiv.ofBijective ρ ⟨(MonoidHom.ker_eq_bot_iff ρ).mp hbot, hρ⟩)
      (hG.mono ht)
  · obtain ⟨f, hf, _hfactor⟩ :=
      CyclicSocleQuotientTools.exists_surjective_factor π hπ ρ hρ
        (hcover ρ.ker inferInstance hbot)
    exact CyclicSocleQuotientTools.socleBound_equiv
      (QuotientGroup.quotientKerEquivOfSurjective f hf) (hQ f.ker inferInstance)

/-- Original normal denominators are retained literally. -/
theorem quotientSocle_of_surjective_normal_cover_quotient
    {G Q : Type} [Group G] [Group Q]
    (π : G →* Q) (hπ : Function.Surjective π) (hker : π.ker ≠ ⊥)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → π.ker ≤ N)
    {t : ℕ} (ht : 1 ≤ t)
    (hQ : ∀ M : Subgroup Q, ∀ _ : M.Normal,
      SocleNormalGeneratorBound (Q ⧸ M) t)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) t :=
  quotientSocle_of_surjective_normal_cover π hπ hker hcover ht hQ
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- Direct form for the original quotient by a displayed normal D. -/
theorem quotientSocle_of_normal_cover
    {G : Type} [Group G] (D : Subgroup G) [D.Normal] (hD : D ≠ ⊥)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → D ≤ N)
    {t : ℕ} (ht : 1 ≤ t)
    (hQ : ∀ M : Subgroup (G ⧸ D), ∀ _ : M.Normal,
      SocleNormalGeneratorBound ((G ⧸ D) ⧸ M) t)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) t := by
  apply quotientSocle_of_surjective_normal_cover_quotient
    (QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D) _ _ ht hQ N
  · simpa only [QuotientGroup.ker_mk'] using hD
  · simpa only [QuotientGroup.ker_mk'] using hcover

end SymmetricSubgroupAsymptotics

end
