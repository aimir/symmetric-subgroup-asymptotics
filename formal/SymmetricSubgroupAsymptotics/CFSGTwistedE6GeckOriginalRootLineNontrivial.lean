import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootFamily
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionParameterTwist

/-! A positive diagram-fixed actual root line has a nonidentity element
in the ORIGINAL model. The literal singleton section at parameter one
is fixed; the actual root-line chart and fixed-U projective injectivity
preserve its nontriviality in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootLineNontrivial
open CFSGTwistedE6GeckOriginalRootFamily CFSGTwistedE6GeckFixedPositiveProjection
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckSectionParameterTwist CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckSectionRootParameters (sectionParameter sectionParameterMulEquiv)
open CFSGNormTwoRootPairing CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGSerreOrdinaryTwists

private theorem image_ne_bot_of_injective_coordinate {U J G : Type*}
    [Group U] [Group J] [Group G] (f : J→*G) (i : U→*J)
    (hfi : Function.Injective (f.comp i)) (S : Subgroup J) (u : U)
    (hu : u≠1) (hS : i u∈S) : S.map f≠⊥ := by
  intro hbot
  have hm : f (i u)∈S.map f := ⟨i u,hS,rfl⟩
  rw [hbot,Subgroup.mem_bot] at hm
  apply hu
  apply hfi
  change f (i u)=(f.comp i) 1
  rw [map_one]
  exact hm

theorem positive_fixed_originalRootLine_ne_bot (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (theta : Roots CartanMatrix.E₆)
    (htheta : ∀i,0≤theta.val i) (hdiagram : diagramRoot theta=theta) :
    originalRootLine q theta≠⊥ := by
  let k : CFSGTwistedE6GeckOriginalRootSections.PositiveRoot := ⟨theta,htheta⟩
  let e := sectionParameterMulEquiv (q.Extension 2) k
  let x := e (Multiplicative.ofAdd (1 : q.Extension 2))
  have hfix : unitTwist (q.Extension 2) (definingFieldAutomorphism q 2) x.val=x.val := by
    change unitTwist (q.Extension 2) (definingFieldAutomorphism q 2)
      (sectionParameter (q.Extension 2) k 1).val=(sectionParameter (q.Extension 2) k 1).val
    rw [singleton_parameter_twist q k hdiagram,map_one]
  have hne : x.val≠1 := by
    intro he
    have hx : x=(1 : CFSGTwistedE6GeckSectionRootParameters.RootLine (q.Extension 2) theta) :=
      Subtype.ext he
    have he' : e (Multiplicative.ofAdd (1 : q.Extension 2))=
        e (1 : Multiplicative (q.Extension 2)) := hx.trans e.map_one.symm
    have hz : (1 : q.Extension 2)=0 :=
      congrArg (fun t : Multiplicative (q.Extension 2)=>t.toAdd) (e.injective he')
    exact one_ne_zero hz
  have hpos : x.val∈Positive (q.Extension 2) :=
    positive_root_subgroup_le CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (q.Extension 2) theta htheta x.property
  let u : signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false := ⟨x.val,⟨hpos,hfix⟩⟩
  have hu : u≠1 := by
    intro he
    exact hne (congrArg (fun z : signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false=>z.val) he)
  have hfi : Function.Injective ((generatedToOriginal q).comp (fixedPositiveToGenerated q)) := by
    intro a b he
    apply fixedPositiveToOriginal_injective q
    exact (fixedPositiveToOriginal_apply q a).trans
      (he.trans (fixedPositiveToOriginal_apply q b).symm)
  exact image_ne_bot_of_injective_coordinate (generatedToOriginal q) (fixedPositiveToGenerated q)
    hfi (rootLineInGenerated q theta) u hu ⟨x.property,hfix⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootLineNontrivial
