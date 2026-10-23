import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFiniteFixedBruhatCover
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveCardinality

/-! The finite fixed Bruhat cover passes through the actual surjection
onto the ORIGINAL model. Only elements, never automorphisms, are lifted. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalFiniteBruhatCover
open CFSGTrialityGeckFiniteFixedBruhatCover CFSGTrialityD4FiniteWeylMenu
open CFSGTrialityGeckGeneratedOriginalProjection CFSGTrialityGeckOriginalPairNormalizer
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckRootPartCoordinates CFSGTrialityGeckOriginalRootFamily
open CFSGTrialityGeckFixedPositiveCardinality CFSGSerreOrdinaryTwists

def originalMenuWord (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (i:Menu) : CFSG.Models.TrialityD4 q :=
  generatedToOriginal q ⟨menuMatrix (q.Extension 3) i,
    menuMatrix_mem_generated _ (definingFieldAutomorphism q 3) i⟩

theorem exists_original_finite_cell (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (g:CFSG.Models.TrialityD4 q) :
    ∃u:(originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)),
      ∃d:originalPairNormalizer q,∃i:Menu,
      ∃v:(originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)),
        g=u.val*d.val*originalMenuWord q i*v.val := by
  obtain ⟨x,rfl⟩ := generatedToOriginal_surjective q g
  obtain ⟨u,hu,d,hd,i,v,hv,he⟩ := exists_finite_fixed_cell
    (q.Extension 3) (definingFieldAutomorphism q 3) x.val x.property
  let U : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) :=
    ⟨u,signedFixed_le_generated _ _ false hu⟩
  let D : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) := ⟨d,hd.2⟩
  let V : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) :=
    ⟨v,signedFixed_le_generated _ _ false hv⟩
  let W : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) :=
    ⟨menuMatrix (q.Extension 3) i,menuMatrix_mem_generated _ _ i⟩
  have huO : generatedToOriginal q U∈(originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)) := by
    rw [←rootPart_positive_original_image]
    exact ⟨U,hu,rfl⟩
  have hvO : generatedToOriginal q V∈(originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)) := by
    rw [←rootPart_positive_original_image]
    exact ⟨V,hv,rfl⟩
  have hdO : generatedToOriginal q D∈originalPairNormalizer q :=
    (mem_originalPairNormalizer_iff q D).mpr hd
  refine ⟨⟨_,huO⟩,⟨_,hdO⟩,i,⟨_,hvO⟩,?_⟩
  have hx : x=U*D*W*V := Subtype.ext he
  have hm := congrArg (generatedToOriginal q) hx
  simpa only [map_mul,originalMenuWord,W] using hm

theorem originalSylow_card_le (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Nat.card (originalSylow q)≤q.order^12 := by
  let P := rootPart (q.Extension 3) (definingFieldAutomorphism q 3) false
  have hm : Nat.card (P.map (generatedToOriginal q))≤Nat.card P :=
    Nat.card_le_card_of_surjective ((generatedToOriginal q).subgroupMap P)
      ((generatedToOriginal q).subgroupMap_surjective P)
  have hc : Nat.card P=q.order^12 :=
    (Nat.card_congr (positivePartEquiv _ _).toEquiv).trans (fixedPositive_card q)
  change Nat.card (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q))≤_
  rw [←rootPart_positive_original_image]
  exact hm.trans_eq hc

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalFiniteBruhatCover
