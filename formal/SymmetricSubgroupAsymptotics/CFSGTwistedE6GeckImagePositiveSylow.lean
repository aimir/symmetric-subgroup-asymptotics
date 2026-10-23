import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOppositeActionImages

/-! A named Sylow in the SAME original Derived action range is exactly
the image of the genuinely fixed positive root part of J. This identifies
concrete subgroup images; it assumes no faithfulness of the source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckImagePositiveSylow
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckFixedPositiveSylow
open CFSGTwistedE6GeckDerivedSylowNormalizer CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGTwistedE6GeckFixedRangePreimage
open CFSGTwistedE6OriginalGoodSylow CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

def imagePositiveSylow (q : CFSG.PrimePower) : Sylow q.prime (derivedImageAction q).range :=
  (preimageSylow q).mapSurjective (f:=preimageToImage q) (preimageToImage_surjective q)

theorem imagePositiveSylow_coe (q : CFSG.PrimePower) :
    (imagePositiveSylow q : Subgroup (derivedImageAction q).range)=
      (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false).map (generatedToDerived q) := by
  simp only [imagePositiveSylow,Sylow.coe_mapSurjective]
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    change x.val∈(fixedPositiveSylow q : Subgroup (MatrixFixed q)) at hx
    rw [fixedPositiveSylow_coe] at hx
    have hpos : x.val.val.val∈Positive (q.Extension 2) := hx
    have hf := congrArg (fun z : MatrixGroup (q.Extension 2)=>z.val) x.val.property
    change unitTwist (q.Extension 2) (definingFieldAutomorphism q 2) x.val.val.val=x.val.val.val at hf
    have hsign : x.val.val.val∈signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false :=
      ⟨hpos,hf⟩
    let j : fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) :=
      ⟨x.val.val.val,signedFixed_le_generated (q.Extension 2) (definingFieldAutomorphism q 2) false hsign⟩
    refine ⟨j,hsign,?_⟩
    apply Subtype.ext
    rfl
  · rintro ⟨j,hj,rfl⟩
    let g : MatrixGroup (q.Extension 2) :=
      Subgroup.inclusion (fixedRootGenerated_le_matrixGroup (q.Extension 2) (definingFieldAutomorphism q 2)) j
    let gf : MatrixFixed q := ⟨g,by
      apply Subtype.ext
      exact hj.2⟩
    have hgf : gf∈FixedUpper q := hj.1
    let x : naturalDerivedPreimage q := ⟨gf,fixed_upper_le_preimage q hgf⟩
    refine ⟨x,?_,?_⟩
    · change gf∈(fixedPositiveSylow q : Subgroup (MatrixFixed q))
      rw [fixedPositiveSylow_coe]
      exact hgf
    · apply Subtype.ext
      rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckImagePositiveSylow
