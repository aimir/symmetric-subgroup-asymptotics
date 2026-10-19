import SymmetricSubgroupAsymptotics.DegreeTwelveCanonicalCatalogueLocator
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenCanonicalCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightCanonicalCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFlexibleResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenStructuralCompleteCatalogue

/-! Two valid branches of the actual degree-sixteen geometric cover.
Bare point classification constructs every required original frame and
natural-module correspondence. No whole-catalogue sixteen-point locator
is assumed. The quartet and two-eight branches are handled separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Pointwise Classical
namespace SymmetricSubgroupAsymptotics

namespace BinaryPairFrame
variable {X : Type} {U : Subgroup (Equiv.Perm X)} {s : ℕ}
    (F : BinaryPairFrame U (Fin s)) (g : Equiv.Perm (Fin s))

theorem reindexed_top_range :
    (F.reindex g).top.range=MulAut.conj g • F.top.range := by
  change (g.permCongrHom.toMonoidHom.comp F.top).range=_
  rw [MonoidHom.range_comp,Subgroup.pointwise_smul_def]
  congr 1

end BinaryPairFrame

namespace DegreeSixteenActualPairPrimitiveSources
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable (p : PreE7PairActionClass 16)
    (F : BinaryPairFrame (preE7PairAction 16 p) (Fin 16))

/-- An actual second pair frame is located in the already checked 24
outer tops by the bare degree-eight classification. -/
def pair_source
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (E : BinaryPairFrame F.top.range (Fin 8)) :
    PreE7RankTailSourceOrYonedaTopData 32
      (preE7SmallPairNonPairAction 16 (by decide) p) := by
  apply Classical.choice
  letI : MulAction.IsPretransitive (preE7PairAction 16 p) (Fin 32) :=
    preE7PairAction_pretransitive 16 p
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have ht : ¬IsPGroup 2 F.top.range :=
    F.top_not_isPGroup (preE7PairAction_not_isPGroup 16 p)
  have htrans : PermutationSubgroupTransitive E.top.range := by
    letI := E.top_pretransitive
    intro i k
    obtain ⟨a,ha⟩ := MulAction.exists_smul_eq E.top.range i k
    exact ⟨a.val,a.property,ha⟩
  obtain ⟨j,g,hg⟩ := DegreeEightCanonicalCatalogue.originalClassification published
    E.top.range htrans (E.top_not_isPGroup ht)
  have he : (E.reindex g).top.range=(DegreeTwoPairedEightSharedTops.interface j).top :=
    (E.reindexed_top_range g).trans hg
  let R : DegreeTwoPairTopTowerRealization (DegreeTwoPairedEightSharedTops.interface j) p :=
    { frame := F, secondFrame := E.reindex g,
      topEquiv := MulEquiv.subgroupCongr he.symm,
      module_action_eq := by intro a v; rfl }
  exact ⟨(DegreeTwoPairedEightCompleteCatalogue.resolvedRow hZmud lit j R).source (by decide)⟩

private theorem primitive_literal_top (j : Fin 20) :
    PrimitiveAffineSixteenAllLiteralFrames.top ⟨j.val,by omega⟩ =
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.primitive16 j).top := by
  fin_cases j <;> rfl

/-- Only the twenty existing primitive rows and the two natural rows are
used here, precisely within the primitive scope of the published input. -/
def primitive_source
    (published : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hp : MulAction.IsPreprimitive F.top.range (Fin 16)) :
    PreE7RankTailSourceOrYonedaTopData 32
      (preE7SmallPairNonPairAction 16 (by decide) p) := by
  apply Classical.choice
  obtain ⟨j,g,hg⟩ := PrimitiveSixteenCanonicalCatalogue.originalClassification
    published F.top.range hp
  let resolve := DegreeTwoFlexibleResidualAssembly.sixteenResolution
    (DegreeTwoSixteenStructuralCompleteCatalogue.remainingData socle hMN) hZmud lit
  by_cases hj : j.val<20
  · let k : Fin 20 := ⟨j.val,hj⟩
    have he : MulAut.conj g • F.top.range=
        (DegreeTwoSixteenPairFiniteCatalogue.catalogue.primitive16 k).top :=
      hg.trans (primitive_literal_top k)
    let R := DegreeTwelveCanonicalCatalogueLocator.realization F
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.primitive16 k) g he
    exact ⟨(resolve.primitive16 k p R).source (by decide)⟩
  · have hcases : j=(20 : Fin 22) ∨ j=(21 : Fin 22) := by
      have hv : j.val=20 ∨ j.val=21 := by omega
      exact hv.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
    rcases hcases with h | h
    · subst j
      change MulAut.conj g • F.top.range=alternatingGroup (Fin 16) at hg
      let R : DegreeTwoSixteenNaturalTopRealization .alternating p :=
        { frame := F.reindex g, top_eq := (F.reindexed_top_range g).trans hg }
      exact ⟨resolve.natural .alternating p R⟩
    · subst j
      change MulAut.conj g • F.top.range=(⊤ : Subgroup (Equiv.Perm (Fin 16))) at hg
      let R : DegreeTwoSixteenNaturalTopRealization .symmetric p :=
        { frame := F.reindex g, top_eq := (F.reindexed_top_range g).trans hg }
      exact ⟨resolve.natural .symmetric p R⟩

end DegreeSixteenActualPairPrimitiveSources
end SymmetricSubgroupAsymptotics
