import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicOuterCentralizer
import SymmetricSubgroupAsymptotics.InjectiveSubgroupCentralizerLift
import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicRadicalOrderedTail
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDerivedInversionFacts

/-! Centralization in the intrinsic Tits flag lifts to literal
centralization of the SAME original ordered tail. Only the checked
injectivity of the full-centre quotient on that source intersection is
used. No automorphism of Tits is lifted to the ambient fixed group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicOuterCentralizerLift
open CFSGTitsIntrinsicOuterCentralizer CFSGTitsIntrinsicFirstLayer
open CFSGTitsIntrinsicMiddleRadical CFSGTitsAmbientPairAlignment
open CFSGReeFFourOuterCentralizingReflection CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourMiddlePositiveIntersectionNormalizer CFSGReeFFourFixedDerivedInversionFacts
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourBinaryPositiveOrderedParameters CFSGTitsIntrinsicRadicalOrderedTail
open CFSGOpposedPeelingOrderedParameters CFSGReeFFourInversionPeelingWords
private abbrev D := commutator (originalModelFixed 0)
private def kSource : D := ⟨reflectionWord 0,reflectionWord_mem_derived 0⟩

private theorem five_normalizes (m : ℕ) : fiveWord m∈Subgroup.normalizer
    (middlePositiveIntersection m : Set (originalModelFixed m)) := by
  change middleFixedWeyl m*(fourCycle m)^2∈_
  exact (Subgroup.normalizer (middlePositiveIntersection m : Set (originalModelFixed m))).mul_mem
    (middle_weyl_normalizes_intersection m)
    (positive_le_normalizer_middle_intersection m (middle_square_positive_derived m).1)

theorem reflectionWord_normalizes_intersection (m : ℕ) :
    reflectionWord m∈Subgroup.normalizer
      (middlePositiveIntersection m : Set (originalModelFixed m)) :=
  (Subgroup.normalizer (middlePositiveIntersection m : Set (originalModelFixed m))).mul_mem
    ((Subgroup.normalizer (middlePositiveIntersection m : Set (originalModelFixed m))).mul_mem
      (five_normalizes m)
      (positive_le_normalizer_middle_intersection m (middle_square_positive_derived m).1))
    ((Subgroup.normalizer (middlePositiveIntersection m : Set (originalModelFixed m))).inv_mem
      (five_normalizes m))

private theorem kSource_normalizes : kSource∈Subgroup.normalizer (sourceIntersection : Set D) :=
  (middlePositiveIntersection 0).le_normalizer_comap D.subtype
    (reflectionWord_normalizes_intersection 0)

private theorem restricted_injective : Function.Injective
    ((derivedReeHom 0).comp sourceIntersection.subtype) := sourceHom_injective

private theorem kSource_value : outerReflection=derivedReeHom 0 kSource := outerReflection_value

private theorem map_commute_transfer {G H : Type*} [Group G] [Group H]
    (f : G→*H) (k u : G) (a x : H) (hk : a=f k) (hu : f u=x)
    (hc : Commute a x) : Commute (f k) (f u) :=
  Eq.mp (congrArg (fun z : H=>Commute z (f u)) hk)
    (Eq.mpr (congrArg (fun z : H=>Commute a z) hu) hc)

theorem exists_original_commuting_lift (x : CFSG.Models.Tits)
    (hx : x∈outerCentralizerFlag) :
    ∃u : sourceIntersection,derivedReeHom 0 u.val=x ∧
      Commute (reflectionWord 0) (u.val : originalModelFixed 0) := by
  have hmap : x∈sourceIntersection.map (derivedReeHom 0) :=
    Eq.mpr (congrArg (fun T : Subgroup CFSG.Models.Tits=>x∈T) sourceIntersection_image) hx.1
  obtain ⟨u,hu,he⟩ := hmap
  have hc : Commute outerReflection x :=
    (Subgroup.mem_centralizer_iff.mp hx.2) outerReflection (Set.mem_singleton outerReflection)
  have hm : Commute (derivedReeHom 0 kSource) (derivedReeHom 0 u) :=
    map_commute_transfer (derivedReeHom 0) kSource u outerReflection x kSource_value he hc
  have hd : Commute kSource u :=
    InjectiveSubgroupCentralizerLift.commute_of_map (derivedReeHom 0) sourceIntersection
      restricted_injective kSource u kSource_normalizes hu hm
  exact ⟨⟨u,hu⟩,he,hd.map D.subtype⟩

theorem exists_original_commuting_parameters (x : CFSG.Models.Tits)
    (hx : x∈outerCentralizerFlag) :
    ∃u : sourceIntersection,derivedReeHom 0 u.val=x ∧
      ∃a : ∀j : Fin 8,Fin (blockPeriod j),
        (a 0).val=0 ∧
        (u.val : originalModelFixed 0)=
          orderedProduct (step 0 true) 8 (fun j=>(blockBase j)^(a j).val) ∧
        Commute (reflectionWord 0)
          (orderedProduct (step 0 true) 8 (fun j=>(blockBase j)^(a j).val)) := by
  obtain ⟨u,hu,hc⟩ := exists_original_commuting_lift x hx
  obtain ⟨a,ha,hfirst⟩ := binary_middle_intersection_power_cover
    (u.val : originalModelFixed 0) u.property
  exact ⟨u,hu,a,hfirst,ha,
    Eq.mp (congrArg (fun z : originalModelFixed 0=>Commute (reflectionWord 0) z) ha) hc⟩

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicOuterCentralizerLift
