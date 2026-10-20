import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectSubgroup
import SymmetricSubgroupAsymptotics.NormalCoverQuotientSocles

/-! All-quotient socle bounds lift through actual faithful irreducible affine
subgroups without assuming uniform normal-generator bounds on their image.
The actual translation kernel is either zero or full; no splitting of the
original subgroup or original normal denominator is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectSubgroup
open SemidirectProduct

variable {V H Q : Type} [CommGroup V] [Nontrivial V] [Group H] [Group Q]
  (φ : H →* MulAut V) (K : Subgroup (V ⋊[φ] H))

theorem socle_of_surjective_of_image_quotients
    (hfaith : Function.Injective (imageAction φ K))
    (hirr : IrreducibleAbelianSemidirect.Irreducible (imageAction φ K))
    {t : ℕ} (ht : 1 ≤ t)
    (himage : ∀ N : Subgroup (Image φ K), ∀ _ : N.Normal,
      SocleNormalGeneratorBound (Image φ K ⧸ N) t)
    (π : K →* Q) (hπ : Function.Surjective π) : SocleNormalGeneratorBound Q t := by
  rcases translations_eq_bot_or_top φ K hirr with hbot | htop
  · let e := projectionEquiv φ K hbot
    let f : Image φ K →* Q := π.comp e.symm.toMonoidHom
    have hf : Function.Surjective f := hπ.comp e.symm.surjective
    exact CyclicSocleQuotientTools.socleBound_equiv
      (QuotientGroup.quotientKerEquivOfSurjective f hf) (himage f.ker inferInstance)
  · let e := actualEquiv φ K htop
    let ψ := imageAction φ K
    let pr : (V ⋊[ψ] Image φ K) →* Image φ K := rightHom
    have hker : pr.ker ≠ ⊥ := by
      obtain ⟨v,hv⟩ := exists_ne (1 : V)
      intro hb
      have hm : (inl v : V ⋊[ψ] Image φ K) ∈ pr.ker := by rfl
      have he : (inl v : V ⋊[ψ] Image φ K) = 1 := Subgroup.mem_bot.mp (hb ▸ hm)
      exact hv (inl_injective (he.trans (map_one inl).symm))
    exact quotientSocle_of_surjective_normal_cover pr rightHom_surjective hker
      (IrreducibleAbelianSemidirect.normal_cover ψ hfaith hirr) ht himage
      (π.comp e.symm.toMonoidHom) (hπ.comp e.symm.surjective)

theorem quotientSocle_of_image_quotients
    (hfaith : Function.Injective (imageAction φ K))
    (hirr : IrreducibleAbelianSemidirect.Irreducible (imageAction φ K))
    {t : ℕ} (ht : 1 ≤ t)
    (himage : ∀ N : Subgroup (Image φ K), ∀ _ : N.Normal,
      SocleNormalGeneratorBound (Image φ K ⧸ N) t)
    (N : Subgroup K) [N.Normal] : SocleNormalGeneratorBound (K ⧸ N) t :=
  socle_of_surjective_of_image_quotients φ K hfaith hirr ht himage
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectSubgroup

end
