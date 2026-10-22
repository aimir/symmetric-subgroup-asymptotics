import SymmetricSubgroupAsymptotics.CFSGTwistedE6CharTwoWords
import SymmetricSubgroupAsymptotics.CFSGA2SingerDerivedImageLift
import SymmetricSubgroupAsymptotics.CFSGTwistedE6DerivedRootImages

/-! The selected original E6 matrix commutators lift through the ACTUAL
fixed-subgroup action to the literal derived fixed subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
open CFSGSerreQuadraticMatrix CFSGExceptionalGeckIntegralData
open CFSGExceptionalNormTwoBases CFSGNormTwoRootPairing
open CFSGA2SingerGeneratedDerived CFSGA2SingerDerivedImageLift
local instance twistedE6CharTwoDerivedImagesDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

private theorem selected_le_canonical (q : CFSG.PrimePower) :
    selectedGroup (charTwoRoots q)≤canonicalElementaryGroup E6Data (q.Extension 2) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨p,rfl⟩
  exact (naturalRoot q p.1 p.2.rev 1).property

def charTwoSelectedAction (q : CFSG.PrimePower) :=
  (canonicalAction q).comp (Subgroup.inclusion (selected_le_canonical q))

theorem charTwoSelectedAction_root (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2) :
    charTwoSelectedAction q (rootLift (charTwoRoots q) neg i)=
      canonicalAction q (naturalRoot q neg i.rev 1) := rfl

theorem exists_charTwoDerivedRoot_image (q : CFSG.PrimePower) [CharP (q.Extension 2) 2]
    (neg : Bool) : ∃x : Derived q,
      derivedImageAction q x=imageAction q (root q neg 1 1 (one_fixed q)) := by
  have hsource : ∀neg i,charTwoSelectedAction q (rootLift (charTwoRoots q) neg i)∈(imageAction q).range := by
    intro neg i
    refine ⟨root q neg i.rev 1 (one_fixed q),?_⟩
    rw [charTwoSelectedAction_root,imageAction_root_eq_canonical]
  obtain ⟨x,hx⟩ := CFSGA2SingerDerivedImageLift.exists_original_derived_preimage
    (charTwoRoots q) (charTwoOmega q) (charTwoRoots_square q)
    (charTwoRoots_braid q) (charTwoRoots_singer q) (charTwoRoots_opposition q)
    (charTwoSelectedAction q) (imageAction q) hsource neg
  refine ⟨x,?_⟩
  change imageAction q x.val=imageAction q (root q neg 1 1 (one_fixed q))
  rw [imageAction_root_eq_canonical]
  simpa only [charTwoSelectedAction_root] using hx

def charTwoDerivedRootLift (q : CFSG.PrimePower) [CharP (q.Extension 2) 2] (neg : Bool) : Derived q :=
  Classical.choose (exists_charTwoDerivedRoot_image q neg)

theorem charTwoDerivedRoot_image (q : CFSG.PrimePower) [CharP (q.Extension 2) 2] (neg : Bool) :
    derivedImageAction q (charTwoDerivedRootLift q neg)=imageAction q (root q neg 1 1 (one_fixed q)) :=
  Classical.choose_spec (exists_charTwoDerivedRoot_image q neg)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
