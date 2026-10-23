import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootFamily
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveSections

/-! Parameter one in a positive diagram-fixed E6 root line is a genuine
nonidentity folded F4 matrix. Its positive projective injectivity proves
nontriviality of the corresponding ORIGINAL F4 root-line image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootLineNontrivial
open CFSGFFourE6OriginalRootFamily CFSGFFourE6FixedPositiveProjection
open CFSGFFourE6OriginalProjection CFSGFFourE6PositiveSections CFSGFFourE6DiagramFixed
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckSectionRootParameters (sectionParameterMulEquiv)
open CFSGTwistedE6WeylChamber CFSGNormTwoRootPairing
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGExceptionalCartanPositiveDefinite
open CFSG.Models.Chevalley

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

theorem positive_fixed_originalRootLine_ne_bot (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (theta : Roots CartanMatrix.E₆) (htheta : ∀i,0≤theta.val i)
    (hdiagram : diagramRoot theta=theta) : originalRootLine K theta≠⊥ := by
  let k : CFSGTwistedE6GeckOriginalRootSections.PositiveRoot := ⟨theta,htheta⟩
  let e := sectionParameterMulEquiv K k
  let x := e (Multiplicative.ofAdd (1 : K))
  have hfolded := singleton_root_mem_folded K k hdiagram x
  have hfix := foldedModel_le_diagramFixed K hfolded
  have hne : x.val≠1 := by
    intro he
    have hx : x=(1 : CFSGTwistedE6GeckSectionRootParameters.RootLine K theta) := Subtype.ext he
    have he' : e (Multiplicative.ofAdd (1 : K))=e (1 : Multiplicative K) := hx.trans e.map_one.symm
    have hz : (1 : K)=0 := congrArg (fun t : Multiplicative K=>t.toAdd) (e.injective he')
    exact one_ne_zero hz
  have hpos : x.val∈Positive K :=
    positive_root_subgroup_le CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K theta htheta x.property
  let u : signedFixed K (RingEquiv.refl K) false := ⟨x.val,⟨hpos,hfix⟩⟩
  have hu : u≠1 := by
    intro he
    exact hne (congrArg (fun z : signedFixed K (RingEquiv.refl K) false=>z.val) he)
  have hfi : Function.Injective ((foldedToOriginal K).comp (fixedPositiveToFolded K)) := by
    intro a b he
    apply fixedPositiveToOriginal_injective K p
    exact (fixedPositiveToOriginal_apply K p a).trans
      (he.trans (fixedPositiveToOriginal_apply K p b).symm)
  exact image_ne_bot_of_injective_coordinate (foldedToOriginal K) (fixedPositiveToFolded K)
    hfi (rootLineInFolded K theta) u hu ⟨x.property,hfix⟩

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootLineNontrivial
