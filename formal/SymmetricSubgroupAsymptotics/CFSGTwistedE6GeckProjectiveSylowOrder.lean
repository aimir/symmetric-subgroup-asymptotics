import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckImagePositiveSylow
import SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveOrderStrict

/-! The two actual opposite image Sylows survive the central quotient.
Their nontriviality yields a strict square-order margin for the ORIGINAL
twisted E6 model, without an exact unipotent order or root census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckProjectiveSylowOrder
open CFSGTwistedE6GeckImagePositiveSylow CFSGTwistedE6GeckOppositeActionImages
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckRelativeOpposition CFSGTwistedE6GeckGeneratedActionImage
open CFSGTwistedE6OriginalGoodSylow CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists
open CFSGTwistedE6GeckDerivedSylowNormalizer CFSGTwistedE6GeckDerivedProjectiveImage
open CFSGTwistedE6GeckSingletonDerivedSeeds CFSGTwistedE6GeckFixedPositiveNoncommute
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance (q : CFSG.PrimePower) : Finite (derivedImageAction q).range :=
  Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)

def oppositionInGenerated (q : CFSG.PrimePower) :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  ⟨relativeOpposition (q.Extension 2),
    relativeOpposition_mem_generated (q.Extension 2) (definingFieldAutomorphism q 2)⟩

def oppositionInDerived (q : CFSG.PrimePower) : (derivedImageAction q).range :=
  generatedToDerived q (oppositionInGenerated q)

def imageOppositeSylow (q : CFSG.PrimePower) : Sylow q.prime (derivedImageAction q).range :=
  (imagePositiveSylow q).mapSurjective
    (f:=(MulAut.conj (oppositionInDerived q)).toMonoidHom) (MulAut.conj (oppositionInDerived q)).surjective

private theorem conjugate_image_le {G H : Type*} [Group G] [Group H]
    (f : G→*H) (U V : Subgroup G) (w : G)
    (hw : ∀u∈U,w*u*w⁻¹∈V) :
    (U.map f).map (MulAut.conj (f w)).toMonoidHom≤V.map f := by
  rintro _ ⟨_,⟨u,hu,rfl⟩,rfl⟩
  refine ⟨w*u*w⁻¹,hw u hu,?_⟩
  change f (w*u*w⁻¹)=f w*f u*(f w)⁻¹
  rw [map_mul,map_mul,map_inv]

private theorem opposition_part_mem (q : CFSG.PrimePower)
    (j : fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2))
    (hj : j∈rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false) :
    oppositionInGenerated q*j*(oppositionInGenerated q)⁻¹∈
      rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true := by
  change relativeOpposition (q.Extension 2)*j.val*(relativeOpposition (q.Extension 2))⁻¹∈
    signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) true
  rw [←fixed_positive_image_eq_fixed_negative (q.Extension 2) (definingFieldAutomorphism q 2)]
  exact ⟨j.val,hj,rfl⟩

theorem imageOppositeSylow_le_negative (q : CFSG.PrimePower) :
    (imageOppositeSylow q : Subgroup (derivedImageAction q).range)≤
      (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true).map (generatedToDerived q) := by
  change ((imagePositiveSylow q : Subgroup (derivedImageAction q).range).map
    (MulAut.conj (oppositionInDerived q)).toMonoidHom)≤_
  have hmap := congrArg (fun S : Subgroup (derivedImageAction q).range=>
    S.map (MulAut.conj (oppositionInDerived q)).toMonoidHom) (imagePositiveSylow_coe q)
  apply hmap.le.trans
  exact conjugate_image_le (generatedToDerived q) _ _ (oppositionInGenerated q) (opposition_part_mem q)

theorem imageSylows_inf (q : CFSG.PrimePower) :
    (imagePositiveSylow q : Subgroup (derivedImageAction q).range) ⊓
      (imageOppositeSylow q : Subgroup (derivedImageAction q).range)=⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have hpos : a∈(rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false).map
      (generatedToDerived q) := by
    rw [←imagePositiveSylow_coe]
    exact ha.1
  have hh := (show a∈(rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false).map
      (generatedToDerived q) ⊓
      (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true).map (generatedToDerived q)
    from ⟨hpos,imageOppositeSylow_le_negative q ha.2⟩)
  rw [original_derived_opposite_parts_inf,Subgroup.mem_bot] at hh
  exact Subgroup.mem_bot.mpr hh

private theorem subgroup_card_gt_one_of_noncommuting {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) (a b : G) (ha : a∈P) (hab : ¬Commute a b) : 1<Nat.card P := by
  let x : P := ⟨a,ha⟩
  have hne : x≠1 := by
    intro hx
    have h : a=1 := congrArg (fun z : P=>z.val) hx
    exact hab (h.symm ▸ Commute.one_left b)
  letI : Nontrivial P := nontrivial_of_ne x 1 hne
  exact Finite.one_lt_card

private def singletonInGenerated (q : CFSG.PrimePower) (j : Fin 2) :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
  ⟨orbitParameter (q.Extension 2) false (![3,2] j) 1,
    orbitParameter_mem_generated (q.Extension 2) (definingFieldAutomorphism q 2) false
      (![3,2] j) 1 (by simp)⟩

private theorem singletonInGenerated_mem (q : CFSG.PrimePower) (j : Fin 2) :
    singletonInGenerated q j∈rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false :=
  ⟨orbitParameter_mem_upper (q.Extension 2) false (![3,2] j) 1,
    orbitParameter_fixed (q.Extension 2) (definingFieldAutomorphism q 2) false (![3,2] j) 1 (by simp)⟩

private theorem singletonInGenerated_action (q : CFSG.PrimePower) (j : Fin 2) :
    (generatedToDerived q (singletonInGenerated q j)).val=
      imageAction q (root q false j 1 (one_fixed q)) := by
  fin_cases j
  · change CFSGTwistedE6GeckSourceAction.matrixAction (q.Extension 2)
      (matrixSingletonRoot q false 0 1)=imageAction q (root q false 0 1 (one_fixed q))
    exact (singleton_root_action q false 0 1 (one_fixed q)).symm
  · change CFSGTwistedE6GeckSourceAction.matrixAction (q.Extension 2)
      (matrixSingletonRoot q false 1 1)=imageAction q (root q false 1 1 (one_fixed q))
    exact (singleton_root_action q false 1 1 (one_fixed q)).symm

private theorem not_commute_of_map_values {G H : Type*} [Group G] [Group H]
    (f : G→*H) (a b : G) (x y : H) (ha : f a=x) (hb : f b=y)
    (hxy : ¬Commute x y) : ¬Commute a b := by
  intro h
  have hh : f a*f b=f b*f a := by rw [←map_mul,←map_mul,h.eq]
  rw [ha,hb] at hh
  exact hxy hh

theorem imagePositiveSylow_card_gt_one (q : CFSG.PrimePower) :
    1<Nat.card (imagePositiveSylow q) := by
  apply subgroup_card_gt_one_of_noncommuting (imagePositiveSylow q : Subgroup (derivedImageAction q).range)
    (generatedToDerived q (singletonInGenerated q 0)) (generatedToDerived q (singletonInGenerated q 1))
  · rw [imagePositiveSylow_coe]
    exact ⟨singletonInGenerated q 0,singletonInGenerated_mem q 0,rfl⟩
  · exact not_commute_of_map_values (derivedImageAction q).range.subtype
      (generatedToDerived q (singletonInGenerated q 0)) (generatedToDerived q (singletonInGenerated q 1))
      (imageAction q (root q false 0 1 (one_fixed q))) (imageAction q (root q false 1 1 (one_fixed q)))
      (singletonInGenerated_action q 0) (singletonInGenerated_action q 1)
      (singleton_fixed_actions_not_commute q)

theorem original_positive_sylow_square_lt_order (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Nat.card (imagePositiveSylow q)^2<Nat.card (CFSG.Models.TwistedE6 q) := by
  have h := CFSGDisjointSylowProjectiveOrder.quotient_center_card_strict_lower
    (imagePositiveSylow q) (imageOppositeSylow q) (imageSylows_inf q)
    (imagePositiveSylow_card_gt_one q)
  rw [Nat.card_congr (originalProjectiveImageEquiv q).toEquiv]
  exact h

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckProjectiveSylowOrder
