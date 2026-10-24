import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedMiddleField
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedOuterField
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalCommonPositiveActions
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedBlockGeneration
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityNormalForms
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsBounds

/-! Actual outer classes of the original Ree quotient are counted by
their common field map after actual inner normalization. The same map
acts on all four signed root blocks, which generate the original group.
Neither a quotient automorphism lift nor positive-only faithfulness is
assumed. The Tits parameter remains separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterBound
open PrimitiveSocleRawStructure CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalPairRestriction CFSGReeFFourOriginalPositiveNormalization
open CFSGReeFFourOriginalCommonPositiveField CFSGReeFFourOriginalCommonPositiveActions
open CFSGReeFFourOriginalSignedOuterField CFSGReeFFourOriginalSignedMiddleField
open CFSGReeFFourOriginalSignedBlockGeneration CFSGReeFFourOriginalSignedRootAction
open CFSGReeFFourOriginalRootCoordinates CFSGReeFFourOriginalRootIntersections
open CFSGReeFFourOriginalNegativeRootIntersections CFSGReeFFourOriginalNegativeOuterCoordinates
open CFSGReeFFourOriginalNegativeMiddleCoordinates CFSGReeFFourOriginalNegativeMiddleRestriction
open CFSGReeFFourOriginalMiddleSemilinear CFSGReeFFourOriginalOuterSemilinear
open CFSGReeFFourOriginalMiddleTorusAction CFSGReeFFourOuterTorusAction
open CFSGReeFFourOriginalPairAlignment CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourOriginalOppositeAlignment CFSGSubgroupFamilyStabilizer

theorem normalized_aut_unique (m : ℕ) (hm : 0<m) (f g : pairStabilizer m hm)
    (tau : Field m ≃+* Field m)
    (hf : positiveLayerDescription m hm f tau tau)
    (hg : positiveLayerDescription m hm g tau tau) : f.val=g.val := by
  apply original_aut_ext_of_signed_root_blocks m hm
  intro neg b x hx
  cases neg <;> cases b
  · change x∈originalRootBlock m hm false at hx
    rw [original_outer_block_eq_range] at hx
    obtain ⟨a,rfl⟩ := hx
    have hfa := (outerRestriction_intertwines m hm f a.toAdd).symm
    have hga := (outerRestriction_intertwines m hm g a.toAdd).symm
    exact hfa.trans ((congrArg (fun z : Field m=>
      originalOuterHom m hm (Multiplicative.ofAdd z))
        ((hf.1 a.toAdd).trans (hg.1 a.toAdd).symm)).trans hga.symm)
  · change x∈originalRootBlock m hm true at hx
    let y : originalRootBlock m hm true := ⟨x,hx⟩
    have heq : middleAction m hm f=middleAction m hm g :=
      (middleAction_eq_fieldAut m hm f tau hf).trans
        (middleAction_eq_fieldAut m hm g tau hg).symm
    have hv := DFunLike.congr_fun heq (originalMiddleSuzukiEquiv m hm y)
    have hr := (middleRestriction_intertwines m hm f y).symm.trans
      (hv.trans (middleRestriction_intertwines m hm g y))
    exact congrArg (fun z : originalRootBlock m hm true=>z.val)
      ((originalMiddleSuzukiEquiv m hm).injective hr)
  · change x∈originalNegativeRootBlock m hm false at hx
    rw [←originalNegativeOuterHom_range] at hx
    obtain ⟨a,rfl⟩ := hx
    rw [original_negative_outer_field_action m hm f tau hf.1,
      original_negative_outer_field_action m hm g tau hg.1]
  · change x∈originalNegativeRootBlock m hm true at hx
    rw [←originalNegativeMiddleEmbedding_range] at hx
    obtain ⟨a,rfl⟩ := hx
    rw [←negativeMiddleAction_embedding,←negativeMiddleAction_embedding,
      negativeMiddleAction_eq_fieldAut m hm f tau hf,
      negativeMiddleAction_eq_fieldAut m hm g tau hg]

theorem original_outer_card_le_field (m : ℕ) (hm : 0<m)
    [Finite (CFSG.Models.ReeF4 m)] :
    Nat.card (Outer (CFSG.Models.ReeF4 m))≤Nat.card (Field m≃+*Field m) := by
  let P (f : MulAut (CFSG.Models.ReeF4 m)) (tau : Field m≃+*Field m) : Prop :=
    ∃ g : pairStabilizer m hm, g.val=f ∧ positiveLayerDescription m hm g tau tau
  letI : Finite (Field m≃+*Field m) :=
    Finite.of_injective (fun f : Field m≃+*Field m=>fun x : Field m=>f x)
      DFunLike.coe_injective
  apply CFSGOuterCardinalityNormalForms.outer_card_le_of_inner_normal_forms P
  · intro f
    obtain ⟨z,hU,hV⟩ := original_exists_inner_fix_pair m hm f
    let f' : pairStabilizer m hm := ⟨MulAut.conj z*f,by
      intro neg
      cases neg
      · exact hU
      · exact hV⟩
    obtain ⟨w,g,tau,hinner,hfields⟩ := exists_inner_normalized_common_positive_field m hm f'
    refine ⟨w*z,g.val,tau,?_,g,rfl,hfields⟩
    intro x
    have h := hinner x
    change g.val x=w*(z*f x*z⁻¹)*w⁻¹ at h
    exact h.trans (by simp only [mul_inv_rev]; group)
  · intro tau f g hf hg
    obtain ⟨f',rfl,hf'⟩ := hf
    obtain ⟨g',rfl,hg'⟩ := hg
    exact normalized_aut_unique m hm f' g' tau hf' hg'

theorem outer_card_le (m : ℕ) (hm : 0<m)
    [Finite (CFSG.Models.ReeF4 m)] :
    Nat.card (Outer (CFSG.Models.ReeF4 m))≤2*m+1 :=
  (original_outer_card_le_field m hm).trans_eq
    (CFSGFiniteFieldAutomorphisms.card_galoisField_ringAut 2 (2*m+1) (by omega))

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterBound
