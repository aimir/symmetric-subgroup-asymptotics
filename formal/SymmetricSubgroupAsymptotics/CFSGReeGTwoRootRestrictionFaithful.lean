import SymmetricSubgroupAsymptotics.CFSGReeGTwoAlignedAutomorphisms
import SymmetricSubgroupAsymptotics.CFSGRankOneRootRestrictionFaithful

/-! The actual positive derived Sylow is transitive on the other Sylows.
Consequently an original-derived automorphism fixing it pointwise and
preserving its opposite is the identity. No rank-one Gauss relation or
full-fixed-group perfectness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoRootRestrictionFaithful
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoOriginalBorel
open CFSGReeGTwoOriginalTorus CFSGReeGTwoPositiveDerived
open CFSGReeGTwoDerivedBruhat CFSGReeGTwoDerivedPairNormalizer
open CFSGReeGTwoIndexPointUpper CFSGReeGTwoDerivedCenter
open CFSGReeGTwoFixedCardinalitySylow
abbrev Derived (m : ℕ) := commutator (originalModelFixed m)
attribute [local instance] fixedModel_finite

theorem derived_borel_factor (m : ℕ) (hm : 1≤m) (b : Derived m)
    (hb : b∈derivedPointStabilizer m) :
    ∃(u : derivedPositiveSylow m hm) (t : derivedTorus m),b=u.val*t.val := by
  have hbRaw : b.val∈borelGroup m := hb
  obtain ⟨x,hx⟩ := hbRaw
  let u : Derived m := ⟨x.left.val,fixedPositiveGroup_le_commutator m hm x.left.property⟩
  let t : Derived m := u⁻¹*b
  have ht : t∈derivedTorus m := by
    refine ⟨x.right,?_⟩
    change fixedTorusHom m x.right=x.left.val⁻¹*b.val
    rw [←hx,borelHom_apply]
    exact (inv_mul_cancel_left _ _).symm
  refine ⟨⟨u,x.left.property⟩,⟨t,ht⟩,?_⟩
  change b=u*(u⁻¹*b)
  exact (mul_inv_cancel_left _ _).symm

theorem positive_transitive_on_other_sylows (m : ℕ) (hm : 1≤m)
    (Q : Sylow 3 (Derived m)) (hQ : Q≠derivedPositiveSylow m hm) :
    ∃u : derivedPositiveSylow m hm,(u:Derived m) •
      (derivedOpposition m hm • derivedPositiveSylow m hm)=Q := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P := derivedPositiveSylow m hm
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Derived m) P Q
  rcases derived_two_cells m hm g with hb | ⟨b,u,he⟩
  · have hfix : g • P=P := Sylow.smul_eq_iff_mem_normalizer.mpr
      ((derived_borel_normalizer m hm) ▸ hb)
    exact False.elim (hQ (hg.symm.trans hfix))
  · have hu : (u:Derived m) • P=P :=
      Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer u.property)
    rw [he,mul_smul,mul_smul,hu] at hg
    obtain ⟨v,t,hvt⟩ := derived_borel_factor m hm b.val b.property
    have ht : (t:Derived m) • (derivedOpposition m hm • P)=derivedOpposition m hm • P :=
      Sylow.smul_eq_iff_mem_normalizer.mpr ((derivedTorus_le_pair_normalizer m hm t.property).2)
    rw [hvt,mul_smul,ht] at hg
    exact ⟨v,hg⟩

theorem eq_one_of_fixed_positive_and_opposite (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] (f : MulAut (Derived m))
    (hU : (derivedPositiveSylow m hm:Subgroup (Derived m)).map f.toMonoidHom=derivedPositiveSylow m hm)
    (hO : (derivedOpposite m hm).map f.toMonoidHom=derivedOpposite m hm)
    (hfix : ∀u : derivedPositiveSylow m hm,f (u:Derived m)=(u:Derived m)) : f=1 := by
  letI : IsSimpleGroup (Derived m) := (originalReeEquivDerived m hm).symm.isSimpleGroup
  have hw : derivedOpposition m hm • derivedPositiveSylow m hm≠derivedPositiveSylow m hm := by
    intro he
    apply derivedOpposition_not_mem_borel m hm
    exact (derived_borel_normalizer m hm).symm ▸ Sylow.smul_eq_iff_mem_normalizer.mp he
  exact CFSGRankOneRootRestrictionFaithful.eq_one_of_fixed_root_and_opposite
    (derivedPositiveSylow m hm) (derivedOpposition m hm) hw
    (positive_transitive_on_other_sylows m hm) f (Sylow.ext hU) (Sylow.ext hO) hfix

end SymmetricSubgroupAsymptotics.CFSGReeGTwoRootRestrictionFaithful
