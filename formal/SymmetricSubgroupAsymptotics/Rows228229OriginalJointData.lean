import SymmetricSubgroupAsymptotics.Rows228229ActualQuartetCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Rows228229ActualQuartetCoordinates
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open BinaryPlaneWreathIrreducible

private theorem mover_generates : Subgroup.zpowers mover = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
  have he : mover^n = g := Subtype.ext hn
  rw [← he]
  exact Subgroup.zpow_mem_zpowers mover n

private theorem cycle_reaches : ∀ j : Fin 3, ∃ n : ℕ, mover^n • (0 : Fin 3) = j := by
  intro j
  obtain ⟨n,hn⟩ := (show ∀ j : Fin 3, ∃ n : Fin 3, mover^n.val • (0 : Fin 3) = j from
    by decide +kernel) j
  exact ⟨n.val,hn⟩

private def topMap (r : Fin 2) : LinearImage r →* Top :=
  PermutationalWreathProduct.rightHom.comp (LinearImage r).subtype
private theorem top_surjective (r : Fin 2) : Function.Surjective (topMap r) := by
  have hm : topMap r (linearGenerator r 3) = mover := rfl
  have hall : (⊤ : Subgroup Top) ≤ (topMap r).range := by
    rw [← mover_generates]
    exact Subgroup.zpowers_le.mpr ⟨linearGenerator r 3,hm⟩
  exact fun g => hall (Subgroup.mem_top g)

private theorem actual_normal_triples (r : Fin 2) :
    ∀ N : Subgroup (Actual r), N.Normal →
      ∃ x : Fin 3 → Actual r, Subgroup.normalClosure (Set.range x) = N := by
  apply IrreducibleAbelianSemidirectSubgroup.normal_generating_tuples
    action (Actual r) (action_injective.comp Subtype.val_injective) (irreducible r) (by decide : 0 < 3)
  apply BinaryPlaneWreathNormalGenerators.normal_generating_tuples
    (LinearImage r) (top_surjective r) mover (0 : Fin 3) cycle_reaches 1
  intro N hN
  letI := hN
  exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic N

abbrev Original (r : Fin 2) := Subgroup.closure (Set.range (generators r))
theorem quotientSocle_three (r : Fin 2) (N : Subgroup (Original r)) [N.Normal] :
    SocleNormalGeneratorBound (Original r ⧸ N) 3 := by
  let f := (BinaryThreeQuartetLiteralSocles.action (R := Top)).comp (Actual r).subtype
  let pi := GeneratedLiteralImage.toTop f (closureGenerators (lifted r)) (generators r)
    (Equiv.refl _) (closureGenerators_full (lifted r)) (binding r)
  have hpi : Function.Surjective pi := GeneratedLiteralImage.toTop_surjective f
    (closureGenerators (lifted r)) (generators r) (Equiv.refl _)
    (closureGenerators_full (lifted r)) (binding r)
  exact normal_generating_tuples_of_surjective ((QuotientGroup.mk' N).comp pi)
    ((QuotientGroup.mk'_surjective N).comp hpi) (actual_normal_triples r)
    (finiteGroupSocle _) inferInstance

private def row228Joint :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row228Interface 3 1 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row228Interface.normalRegistry (fun N => by letI := N.2; exact quotientSocle_three 0 N.1)
  natural := PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily.row228Natural
private def row229Joint :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row229Interface 3 1 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row229Interface.normalRegistry (fun N => by letI := N.2; exact quotientSocle_three 1 N.1)
  natural := PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily.row229Natural

def row228Data (_socle : PublishedPrimitiveSocleDichotomyInput)
    (_catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row228Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact row228Joint (by decide +kernel)
def row229Data (_socle : PublishedPrimitiveSocleDichotomyInput)
    (_catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row229Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact row229Joint (by decide +kernel)

end SymmetricSubgroupAsymptotics.Rows228229ActualQuartetCoordinates
