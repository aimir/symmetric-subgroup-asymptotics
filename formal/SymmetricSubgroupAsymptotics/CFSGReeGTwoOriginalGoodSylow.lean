import SymmetricSubgroupAsymptotics.CFSGReeGTwoRootGeneratedNormal
import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedCardinalitySylow
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCentralQuotient
import SymmetricSubgroupAsymptotics.CFSGSylowSubgroupNormalizer
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective

/-! Good defining-prime Sylow witnesses for the literal pinned ReeG2.
The full fixed group is not asserted perfect or simple. Its actual two-root
subgroup is normal, lies in the original derived group, and has nontrivial
normal image in the simple original derived/central quotient. That actual
surjective image transfers the two-p-subgroup and normalizer witnesses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalGoodSylow
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoPositiveDerived
open CFSGReeGTwoOriginalOpposition CFSGReeGTwoPositiveCentralQuotient
open CFSGReeGTwoFixedRankOneGeometry CFSGReeGTwoFixedCardinalitySylow
open CFSGReeGTwoRootGeneratedNormal CFSGReduction CFSGSylowSubgroupNormalizer

attribute [local instance] fixedModel_finite

theorem fixedNegativeGroup_isPGroup (m : ℕ) : IsPGroup 3 (fixedNegativeGroup m) :=
  (fixedPositiveGroup_isPGroup m).map (MulAut.conj (fixedOpposition m)).toMonoidHom

theorem fixedRootGenerated_le_commutator (m : ℕ) (hm : 1≤m) :
    fixedRootGenerated m≤commutator (originalModelFixed m) := by
  apply sup_le (fixedPositiveGroup_le_commutator m hm)
  rintro _ ⟨u,hu,rfl⟩
  exact (inferInstance : (commutator (originalModelFixed m)).Normal).conj_mem u
    (fixedPositiveGroup_le_commutator m hm hu) (fixedOpposition m)

def rootDerivedHom (m : ℕ) (hm : 1≤m) :
    fixedRootGenerated m →* commutator (originalModelFixed m) :=
  (fixedRootGenerated m).subtype.codRestrict _
    (fun x => fixedRootGenerated_le_commutator m hm x.property)

def derivedReeHom (m : ℕ) : commutator (originalModelFixed m) →* CFSG.Models.ReeG2 m :=
  (originalReeEquiv m).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center (commutator (originalModelFixed m))))

theorem derivedReeHom_surjective (m : ℕ) : Function.Surjective (derivedReeHom m) :=
  (originalReeEquiv m).symm.surjective.comp (QuotientGroup.mk'_surjective _)

def rootReeHom (m : ℕ) (hm : 1≤m) : fixedRootGenerated m →* CFSG.Models.ReeG2 m :=
  (derivedReeHom m).comp (rootDerivedHom m hm)

theorem rootReeHom_surjective (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] : Function.Surjective (rootReeHom m hm) := by
  let D := commutator (originalModelFixed m)
  let S := (fixedRootGenerated m).subgroupOf D
  let R := S.map (derivedReeHom m)
  have hnS : S.Normal := (fixedRootGenerated_normal m).subgroupOf D
  have hnR : R.Normal := hnS.map (derivedReeHom m) (derivedReeHom_surjective m)
  have hR : R=⊤ := by
    rcases hnR.eq_bot_or_eq_top with hb | ht
    · obtain ⟨u,hu,hne⟩ := fixed_positive_nonidentity m
      have huR : reePositiveHom m hm ⟨u,hu⟩∈R :=
        ⟨positiveDerivedHom m hm ⟨u,hu⟩,positive_le_generated m hu,rfl⟩
      rw [hb] at huR
      have he : reePositiveHom m hm ⟨u,hu⟩=reePositiveHom m hm 1 := by
        simpa only [map_one] using (Subgroup.mem_bot.mp huR)
      exact False.elim (hne (congrArg Subtype.val (reePositiveHom_injective m hm he)))
    · exact ht
  intro g
  have hg : g∈R := hR.symm ▸ Subgroup.mem_top g
  obtain ⟨d,hd,he⟩ := hg
  exact ⟨⟨d.val,hd⟩,he⟩

theorem rootGenerated_goodSylowPrime (m : ℕ) : GoodSylowPrime (fixedRootGenerated m) 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let H := fixedRootGenerated m
  let U := (fixedPositiveGroup m).subgroupOf H
  let V := (fixedNegativeGroup m).subgroupOf H
  have hU : IsPGroup 3 U := (fixedPositiveGroup_isPGroup m).comap_of_injective
    H.subtype H.subtype_injective
  have hV : IsPGroup 3 V := (fixedNegativeGroup_isPGroup m).comap_of_injective
    H.subtype H.subtype_injective
  have hgen : U⊔V=⊤ := by
    have hm : (U⊔V).map H.subtype=H := by
      rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le (positive_le_generated m),
        Subgroup.map_subgroupOf_eq_of_le (show fixedNegativeGroup m≤H from le_sup_right)]
      rfl
    apply top_unique
    intro x _
    have hx : x.val∈(U⊔V).map H.subtype := hm.symm ▸ x.property
    obtain ⟨y,hy,he⟩ := hx
    exact (Subtype.ext he : y=x) ▸ hy
  let P : Sylow 3 H := (fixedPositiveSylow m).subtype (positive_le_generated m)
  have hsol : IsSolvable (Subgroup.normalizer (P:Set H)) :=
    soluble_subgroup_normalizer (fixedPositiveGroup m) H (positive_le_generated m)
      (fixed_positive_normalizer_soluble m)
  exact goodSylowPrime_of_two_p_subgroups_and_exists_soluble_normalizer U V hU hV hgen ⟨P,hsol⟩

theorem reeGTwo_goodSylowPrime (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] : GoodSylowPrime (CFSG.Models.ReeG2 m) 3 :=
  goodSylowPrime_surjective (rootReeHom m hm) (rootReeHom_surjective m hm)
    (rootGenerated_goodSylowPrime m)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalGoodSylow
