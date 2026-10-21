import SymmetricSubgroupAsymptotics.PGroupElementaryAbelianizationRank
import SymmetricSubgroupAsymptotics.AbelianizationSaturationRelativeRadical
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadSurjectiveKernel

/-! Actual ordinary rank additivity, after full abelianization exponent p
has been proved, fills the exact order saturation premise internally.
Every further original derived denominator preserves the actual kernel's
full relative head. These are the equality mechanisms of RDT5.6(ii),
without a split extension or an independently chosen image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable (p : ℕ) [Fact p.Prime]
  {G H : Type} [Group G] [Finite G] [Group H] [Finite H]

/-- The complete source and top abelianization orders saturate the
actual elementary-kernel extension inequality. -/
theorem pGroup_relativeRadical_eq_inf_commutator_of_rank_additivity
    (hG : IsPGroup p G) (f : G →* H) (hf : Function.Surjective f)
    (hpow : ∀ k : f.ker, (k : G)^p=1)
    (hexp : ∀ a : Abelianization G, a^p=1)
    (hrank : MarkedC4.genRank G=MarkedC4.normalGen f.ker+MarkedC4.genRank H) :
    primeRelativeRadical p f.ker=f.ker ⊓ commutator G := by
  have hH := hG.of_surjective f hf
  have hexpH : ∀ a : Abelianization H, a^p=1 := by
    intro a
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (commutator H) a
    obtain ⟨g,rfl⟩ := hf h
    have he := congrArg (Abelianization.map f) (hexp (Abelianization.of g))
    simpa only [map_pow,map_one,Abelianization.map_of] using he
  apply pGroup_relativeRadical_eq_inf_commutator_of_abelianization_saturation
    p hG f hf hpow
  rw [pGroup_abelianization_card_eq_pow_genRank p hG hexp,
    pGroup_abelianization_card_eq_pow_genRank p hH hexpH,hrank,pow_add]

/-- A SAME original denominator below G' kills only the original kernel
radical; no normal-generation monotonicity is invoked. -/
theorem pGroup_kernel_image_relativeHead_of_rank_additivity
    (hG : IsPGroup p G) (f : G →* H) (hf : Function.Surjective f)
    (hpow : ∀ k : f.ker, (k : G)^p=1)
    (hexp : ∀ a : Abelianization G, a^p=1)
    (hrank : MarkedC4.genRank G=MarkedC4.normalGen f.ker+MarkedC4.genRank H)
    (N : Subgroup G) [N.Normal] (hN : N≤commutator G) :
    letI : (f.ker.map (QuotientGroup.mk' N)).Normal :=
      Subgroup.Normal.map inferInstance (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N)
    Module.finrank (ZMod p)
        (primeRelativeCharacters p (f.ker.map (QuotientGroup.mk' N))) =
      Module.finrank (ZMod p) (primeRelativeCharacters p f.ker) := by
  letI : (f.ker.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
  apply primeRelativeHead_map_eq_of_kernel_inf_le_radical p
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) f.ker
  rw [QuotientGroup.ker_mk',
    pGroup_relativeRadical_eq_inf_commutator_of_rank_additivity p hG f hf hpow hexp hrank]
  exact inf_le_inf le_rfl hN

end SymmetricSubgroupAsymptotics
