import SymmetricSubgroupAsymptotics.TwelveInstalledSocleOneSixPairSource
import SymmetricSubgroupAsymptotics.TwelvePrimitiveInstalledSocleOnePilot
import SymmetricSubgroupAsymptotics.TwelveStructuralInstalledSocleOnePilot

/-! Combine proved installed families and the actual capacity-one package
pilots. The union is a reusable source subset, not a six-pair census. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwelveInstalledSocleOneExtendedSource
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def indices : Finset (Fin 301) :=
  TwelveInstalledSocleOneSixPairSource.indices ∪ {7,8,165,178,217}

def source
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (j : Fin 301) (hj : j ∈ indices) (p : PreE7PairActionClass 6)
    (e : (catalogue.row j).finite.top ≃* preE7PairAction 6 p) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) := by
  by_cases hb : j ∈ TwelveInstalledSocleOneSixPairSource.indices
  · exact TwelveInstalledSocleOneSixPairSource.source hZmud j hb p e
  apply Classical.choice
  have ha : j ∈ ({7,8,165,178,217} : Finset (Fin 301)) :=
    (Finset.mem_union.mp hj).resolve_left hb
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact ⟨TwelveStructuralInstalledSocleOnePilot.source socle primitiveCatalogue hZmud 2 p e⟩
  · exact ⟨TwelveStructuralInstalledSocleOnePilot.source socle primitiveCatalogue hZmud 1 p e⟩
  · exact ⟨TwelveStructuralInstalledSocleOnePilot.source socle primitiveCatalogue hZmud 0 p e⟩
  · exact ⟨TwelvePrimitiveInstalledSocleOnePilot.source socle primitiveCatalogue hZmud 0 p e⟩
  · exact ⟨TwelvePrimitiveInstalledSocleOnePilot.source socle primitiveCatalogue hZmud 1 p e⟩

end SymmetricSubgroupAsymptotics.TwelveInstalledSocleOneExtendedSource
