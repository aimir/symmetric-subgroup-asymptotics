import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterCentralizingReflection
import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFiveFaithful
import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicOuterBlocks
import SymmetricSubgroupAsymptotics.CFSGReeFFourSignedOuterOddProduct

/-! An INTERNAL reflection and its centralizer flag in the SAME Tits
radical. The literal pair-fixer fixes the reflection, preserves the flag,
and sends the actual outer root into that flag. No automorphism is lifted
to the full fixed group; no flag cardinality or head rank is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicOuterCentralizer
open CFSGTitsIntrinsicFiveAction CFSGTitsIntrinsicFiveFaithful
open CFSGTitsIntrinsicMiddleSquare CFSGTitsIntrinsicMiddleRadical CFSGTitsAmbientPairAlignment
open CFSGReeFFourOuterCentralizingReflection CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourMiddleDerivedFiveSurvival CFSGReeFFourMiddleSquareCommutator
open CFSGReeFFourSignedOuterOddProduct CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourBinaryOuterSaving
open CFSGTitsIntrinsicOuterBlocks CFSGReeFFourInnerBracketOriginalBlocks
open CFSGReeFFourMiddlePositiveIntersectionNormalizer CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourOuterThreeWord
private abbrev D := commutator (originalModelFixed 0)
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private def reflectionSource : D := ⟨reflectionWord 0,reflectionWord_mem_derived 0⟩

private theorem map_conjugate {G H : Type*} [Group G] [Group H]
    (f : G→*H) (r t k : G) (a b : H)
    (ha : a=f r) (hb : b=f t) (hk : k=r*t*r⁻¹) : a*b*a⁻¹=f k := by
  rw [ha,hb,hk,map_mul,map_mul,map_inv]

def outerReflection : CFSG.Models.Tits :=
  fiveElement*middleSquareRoot*fiveElement⁻¹

theorem outerReflection_value : outerReflection=derivedReeHom 0 reflectionSource := by
  let s : D := ⟨(fourCycle 0)^2,square_mem_derived 0⟩
  have hr : fiveElement=derivedReeHom 0 (derivedFiveWord 0) := fiveElement_original_value
  have hs : middleSquareRoot=derivedReeHom 0 s := middleSquareRoot_value
  have hk : reflectionSource=derivedFiveWord 0*s*(derivedFiveWord 0)⁻¹ := Subtype.ext rfl
  exact map_conjugate (derivedReeHom 0) (derivedFiveWord 0) s reflectionSource
    fiveElement middleSquareRoot hr hs hk

private theorem conjugate_square {G : Type*} [Group G] (r t : G) (ht : t^2=1) :
    (r*t*r⁻¹)^2=1 := by
  calc
    _=r*t^2*r⁻¹ := by simp only [pow_two]; group
    _=1 := by rw [ht]; group

private theorem conjugate_ne_one {G : Type*} [Group G] (r t : G) (ht : t≠1) :
    r*t*r⁻¹≠1 := by
  intro h
  apply ht
  calc
    t=r⁻¹*(r*t*r⁻¹)*r := by group
    _=1 := by rw [h]; group

theorem outerReflection_square : outerReflection^2=1 :=
  conjugate_square fiveElement middleSquareRoot middleSquareRoot_square

theorem outerReflection_order : orderOf outerReflection=2 :=
  orderOf_eq_prime outerReflection_square
    (conjugate_ne_one fiveElement middleSquareRoot middleSquareRoot_ne_one)

theorem pairStabilizer_fixes_outerReflection (f : pairStabilizer) :
    f.val outerReflection=outerReflection := by
  change f.val (fiveElement*middleSquareRoot*fiveElement⁻¹)=
    fiveElement*middleSquareRoot*fiveElement⁻¹
  rw [map_mul,map_mul,map_inv,pairStabilizer_fixes_fiveElement,
    pairStabilizer_fixes_middleSquareRoot]

theorem outerReflection_commutes_outer : Commute outerReflection (originalOuterRoot 0) := by
  have hc : Commute reflectionSource (derivedOuterRoot 0) :=
    show reflectionSource*derivedOuterRoot 0=derivedOuterRoot 0*reflectionSource from
      Subtype.ext (reflectionWord_commutes_outer 0)
  have hm := hc.map (derivedReeHom 0)
  exact Eq.mpr (congrArg (fun k : CFSG.Models.Tits=>Commute k (originalOuterRoot 0))
    outerReflection_value) hm

private theorem conjugate_mem_reverse {G : Type*} [Group G]
    (P : Subgroup G) (w x : G)
    (hw : w∈Subgroup.normalizer (P : Set G))
    (hx : (MulAut.conj w) x∈P) : x∈P :=
  (Subgroup.mem_normalizer_iff.mp hw x).mpr hx

private theorem first_block_value (m : ℕ) :
    actualOuterBlock m 0=(MulAut.conj (middleFixedWeyl m)) (outerInvolution m) := rfl

private theorem outer_intersection (m : ℕ) :
    outerInvolution m∈middlePositiveIntersection m := by
  have hc : (MulAut.conj (middleFixedWeyl m)) (outerInvolution m)∈
      middlePositiveIntersection m :=
    Eq.mp (congrArg (fun x=>x∈middlePositiveIntersection m) (first_block_value m))
      (actualBlock_intersection m 0)
  exact conjugate_mem_reverse (middlePositiveIntersection m) _ _
    (middle_weyl_normalizes_intersection m) hc

private theorem outer_mem_radical : originalOuterRoot 0∈middleRadical :=
  Eq.mp (congrArg (fun T : Subgroup CFSG.Models.Tits=>originalOuterRoot 0∈T)
    sourceIntersection_image)
    ⟨derivedOuterRoot 0,outer_intersection 0,rfl⟩

def outerCentralizerFlag : Subgroup CFSG.Models.Tits :=
  middleRadical⊓Subgroup.centralizer ({outerReflection} : Set CFSG.Models.Tits)

theorem outer_mem_centralizerFlag : originalOuterRoot 0∈outerCentralizerFlag := by
  refine ⟨outer_mem_radical,Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro z hz
  have he : z=outerReflection := Set.mem_singleton_iff.mp hz
  exact he ▸ outerReflection_commutes_outer

private theorem invariant_centralizer_intersection {G : Type*} [Group G]
    (F : MulAut G) (R : Subgroup G) (k : G)
    (hR : R.map F.toMonoidHom=R) (hk : F k=k) :
    (R⊓Subgroup.centralizer ({k} : Set G)).map F.toMonoidHom=
      R⊓Subgroup.centralizer ({k} : Set G) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨Eq.mp (congrArg (fun T : Subgroup G=>F x∈T) hR) ⟨x,hx.1,rfl⟩,
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro a ha
    have he : a=k := Set.mem_singleton_iff.mp ha
    have hc := congrArg F ((Subgroup.mem_centralizer_iff.mp hx.2) k (Set.mem_singleton k))
    simpa only [map_mul,hk,he] using hc
  · intro hz
    obtain ⟨x,hx,he⟩ := Eq.mpr (congrArg (fun T : Subgroup G=>z∈T) hR) hz.1
    refine ⟨x,⟨hx,Subgroup.mem_centralizer_iff.mpr ?_⟩,he⟩
    intro a ha
    have hak : a=k := Set.mem_singleton_iff.mp ha
    rw [hak]
    apply F.injective
    have heF : F x=z := he
    simpa only [map_mul,hk,heF] using
      ((Subgroup.mem_centralizer_iff.mp hz.2) k (Set.mem_singleton k))

theorem pairStabilizer_preserves_outerCentralizerFlag (f : pairStabilizer) :
    outerCentralizerFlag.map f.val.toMonoidHom=outerCentralizerFlag :=
  invariant_centralizer_intersection f.val middleRadical outerReflection
    (pairStabilizer_preserves_middleRadical f) (pairStabilizer_fixes_outerReflection f)

theorem pairStabilizer_outer_image_mem_flag (f : pairStabilizer) :
    f.val (originalOuterRoot 0)∈outerCentralizerFlag :=
  Eq.mp (congrArg (fun T : Subgroup CFSG.Models.Tits=>f.val (originalOuterRoot 0)∈T)
    (pairStabilizer_preserves_outerCentralizerFlag f))
    ⟨originalOuterRoot 0,outer_mem_centralizerFlag,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicOuterCentralizer
