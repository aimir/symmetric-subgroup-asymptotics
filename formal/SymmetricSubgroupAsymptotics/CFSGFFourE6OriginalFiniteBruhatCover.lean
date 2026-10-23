import SymmetricSubgroupAsymptotics.CFSGFFourE6FiniteFixedBruhatCover
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalPairScalarAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositiveCardinality

/-! The finite fixed Bruhat cover passes through the literal surjection
onto the ORIGINAL F4 model. Only elements are lifted. The positive-factor
cardinality uses the proved actual fixed-height upper bound. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalFiniteBruhatCover
open CFSGFFourE6FiniteFixedBruhatCover CFSGFFourE6FiniteWeylMenu
open CFSGFFourE6GeneratedOriginalProjection CFSGFFourE6OriginalPairScalarAction
open CFSGFFourE6OriginalProjection CFSGFFourE6FixedPositiveCardinality
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckPositiveTwist CFSG.Models.Chevalley

def originalMenuWord (K:Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (i:relativeWeylRange) :
    Projective CartanMatrix.F₄ K :=
  generatedToOriginal K ⟨menuMatrix K i,menuMatrix_mem_generated K (RingEquiv.refl K) i⟩

theorem exists_original_finite_cell (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (g:Projective CartanMatrix.F₄ K) :
    ∃u:(originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)),
      ∃d:originalPairNormalizer K p,∃i:relativeWeylRange,
      ∃v:(originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)),
        g=u.val*d.val*originalMenuWord K i*v.val := by
  obtain ⟨x,rfl⟩ := generatedToOriginal_surjective K g
  obtain ⟨u,hu,d,hd,i,v,hv,he⟩ := exists_finite_fixed_cell
    K (RingEquiv.refl K) x.val x.property
  let U : fixedRootGenerated K (RingEquiv.refl K) :=
    ⟨u,signedFixed_le_generated _ _ false hu⟩
  let D : fixedRootGenerated K (RingEquiv.refl K) := ⟨d,hd.2⟩
  let V : fixedRootGenerated K (RingEquiv.refl K) :=
    ⟨v,signedFixed_le_generated _ _ false hv⟩
  let W : fixedRootGenerated K (RingEquiv.refl K) :=
    ⟨menuMatrix K i,menuMatrix_mem_generated _ _ i⟩
  have huO : generatedToOriginal K U∈
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)) := by
    rw [←rootPart_positive_original_image]
    exact ⟨U,hu,rfl⟩
  have hvO : generatedToOriginal K V∈
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)) := by
    rw [←rootPart_positive_original_image]
    exact ⟨V,hv,rfl⟩
  have hdO : generatedToOriginal K D∈originalPairNormalizer K p :=
    (mem_originalPairNormalizer_iff K p D).mpr hd
  refine ⟨⟨_,huO⟩,⟨_,hdO⟩,i,⟨_,hvO⟩,?_⟩
  have hx : x=U*D*W*V := Subtype.ext he
  have hm := congrArg (generatedToOriginal K) hx
  simpa only [map_mul,originalMenuWord,W] using hm

theorem originalPositiveSylow_card_le (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Nat.card (originalPositiveSylow K p)≤Nat.card K^24 := by
  let P := rootPart K (RingEquiv.refl K) false
  have hm : Nat.card (P.map (generatedToOriginal K))≤Nat.card P :=
    Nat.card_le_card_of_surjective ((generatedToOriginal K).subgroupMap P)
      ((generatedToOriginal K).subgroupMap_surjective P)
  let f : P→CFSGE6GeckFixedTailCardinality.fixedPositive K (RingEquiv.refl K) := fun x=>
    ⟨⟨x.val.val,x.property.1⟩,Subtype.ext x.property.2⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z:CFSGE6GeckFixedTailCardinality.fixedPositive K (RingEquiv.refl K)=>
      z.val.val) he
  have hc : Nat.card P≤Nat.card K^24 :=
    (Nat.card_le_card_of_injective f hf).trans (fixedPositive_card_le K (RingEquiv.refl K))
  change Nat.card (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K))≤_
  rw [←rootPart_positive_original_image]
  exact hm.trans hc

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalFiniteBruhatCover
