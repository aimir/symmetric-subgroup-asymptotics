import SymmetricSubgroupAsymptotics.CFSGFFourE6FiniteFixedBruhatCover
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositiveCardinality

/-! The actual generic-sigma E6 fixed Bruhat cover passes to ORIGINAL
twisted E6 through its own literal J projection. The coarse upper bound
on the actual fixed upper over q^2 suffices; no same-field model is
substituted and no automorphism is lifted. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalFiniteBruhatCover
open CFSGFFourE6FiniteFixedBruhatCover CFSGFFourE6FiniteWeylMenu
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalPairNormalizer
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGFFourE6FixedPositiveCardinality
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckPositiveTwist CFSGSerreOrdinaryTwists

def originalMenuWord (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (i:relativeWeylRange) : CFSG.Models.TwistedE6 q :=
  generatedToOriginal q ⟨menuMatrix (q.Extension 2) i,
    menuMatrix_mem_generated _ (definingFieldAutomorphism q 2) i⟩

theorem exists_original_finite_cell (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (g:CFSG.Models.TwistedE6 q) :
    ∃u:(originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)),
      ∃d:originalPairNormalizer q,∃i:relativeWeylRange,
      ∃v:(originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)),
        g=u.val*d.val*originalMenuWord q i*v.val := by
  obtain ⟨x,rfl⟩ := generatedToOriginal_surjective q g
  obtain ⟨u,hu,d,hd,i,v,hv,he⟩ := exists_finite_fixed_cell
    (q.Extension 2) (definingFieldAutomorphism q 2) x.val x.property
  let U : fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
    ⟨u,signedFixed_le_generated _ _ false hu⟩
  let D : fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) := ⟨d,hd.2⟩
  let V : fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
    ⟨v,signedFixed_le_generated _ _ false hv⟩
  let W : fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
    ⟨menuMatrix (q.Extension 2) i,menuMatrix_mem_generated _ _ i⟩
  have huO : generatedToOriginal q U∈
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)) := by
    rw [←rootPart_positive_original_image]
    exact ⟨U,hu,rfl⟩
  have hvO : generatedToOriginal q V∈
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)) := by
    rw [←rootPart_positive_original_image]
    exact ⟨V,hv,rfl⟩
  have hdO : generatedToOriginal q D∈originalPairNormalizer q :=
    (mem_originalPairNormalizer_iff q D).mpr hd
  refine ⟨⟨_,huO⟩,⟨_,hdO⟩,i,⟨_,hvO⟩,?_⟩
  have hx : x=U*D*W*V := Subtype.ext he
  have hm := congrArg (generatedToOriginal q) hx
  simpa only [map_mul,originalMenuWord,W] using hm

theorem originalPositiveSylow_card_le (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Nat.card (originalPositiveSylow q)≤q.order^48 := by
  let P := rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false
  have hm : Nat.card (P.map (generatedToOriginal q))≤Nat.card P :=
    Nat.card_le_card_of_surjective ((generatedToOriginal q).subgroupMap P)
      ((generatedToOriginal q).subgroupMap_surjective P)
  let f : P→CFSGE6GeckFixedTailCardinality.fixedPositive (q.Extension 2) (definingFieldAutomorphism q 2) :=
    fun x=>⟨⟨x.val.val,x.property.1⟩,Subtype.ext x.property.2⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z:CFSGE6GeckFixedTailCardinality.fixedPositive
      (q.Extension 2) (definingFieldAutomorphism q 2)=>z.val.val) he
  have hc : Nat.card P≤q.order^48 := by
    calc
      Nat.card P≤Nat.card (CFSGE6GeckFixedTailCardinality.fixedPositive
        (q.Extension 2) (definingFieldAutomorphism q 2)) := Nat.card_le_card_of_injective f hf
      _≤Nat.card (q.Extension 2)^24 :=
        fixedPositive_card_le (q.Extension 2) (definingFieldAutomorphism q 2)
      _=q.order^48 := by rw [CFSGTwistedANaturalMatrices.extension_two_card,←pow_mul]
  change Nat.card (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q))≤_
  rw [←rootPart_positive_original_image]
  exact hm.trans hc

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalFiniteBruhatCover
