import SymmetricSubgroupAsymptotics.FourPairTop3NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop4NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop5NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop7NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop8NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop9NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop10NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop18NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop19NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop20NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop21NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop22NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop23NoPairing
import SymmetricSubgroupAsymptotics.FourPairTop24NoPairing
import SymmetricSubgroupAsymptotics.FourPairNormalChainCanonicalRows
import SymmetricSubgroupAsymptotics.FourPairCentralProductCanonicalRows
import SymmetricSubgroupAsymptotics.FourPairY1CanonicalRow
import SymmetricSubgroupAsymptotics.FourPairY2CanonicalRow
import SymmetricSubgroupAsymptotics.FourPairY3CanonicalRow
import SymmetricSubgroupAsymptotics.FourPairY4CanonicalRow
import SymmetricSubgroupAsymptotics.FourPairY5CanonicalRow
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! Complete actual four-pair dispatch from the bare fixed degree-eight
catalogue and the existing Zmud literature theorem. The fourteen excluded
literal actions are ruled out by original point-stabilizer word witnesses;
the other ten receive proved actual models. No certificate-valued catalogue
callback, normal census or numerical source premise is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.FourPairCanonicalClassification
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- Retain the original physical frame under both actual catalogue
conjugacies; the no-pairing obstruction consumes this exact frame. -/
def canonicalFrame (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p)) :
    BinaryPairFrame (DegreeEightCanonicalCatalogue.canonical M.index) (Fin 4) := by
  let A := preE7PairAction 4 p
  let B := relabelSubgroup M.points A
  have hret : relabelSubgroup M.conjugator B =
      (DegreeTwoPairedEightSharedTops.interface M.index).top := by
    calc
      relabelSubgroup M.conjugator B = MulAut.conj M.conjugator • B := by
        change B.map M.conjugator.permCongrHom.toMonoidHom = _
        rw [Subgroup.pointwise_smul_def]
        congr 1
      _ = _ := M.matched
  let F : BinaryPairFrame (DegreeTwoPairedEightSharedTops.interface M.index).top (Fin 4) :=
    hret ▸ ((preE7PairFrame 4 p).relabelPoints M.points).relabelPoints M.conjugator
  have hcan : relabelSubgroup (DegreeEightCanonicalCatalogue.conjugator M.index)
      (DegreeTwoPairedEightSharedTops.interface M.index).top =
        DegreeEightCanonicalCatalogue.canonical M.index := by
    calc
      _ = MulAut.conj (DegreeEightCanonicalCatalogue.conjugator M.index) •
          (DegreeTwoPairedEightSharedTops.interface M.index).top := by
        change (DegreeTwoPairedEightSharedTops.interface M.index).top.map
          (DegreeEightCanonicalCatalogue.conjugator M.index).permCongrHom.toMonoidHom = _
        rw [Subgroup.pointwise_smul_def]
        congr 1
      _ = _ := DegreeEightCanonicalCatalogue.literal_conjugated_eq M.index
  exact hcan ▸ F.relabelPoints (DegreeEightCanonicalCatalogue.conjugator M.index)

/-- The project-owned ten-row classification is now constructed, with
only actual published completeness and the explicit Zmud theorem as inputs. -/
theorem classification (hZmud : ZmudFaithfulCharacterTupleInput)
    (published : DegreeEightCanonicalCatalogue.PublishedClassification) :
    PublishedDegreeTwoFourPairClassification := by
  intro p
  let M := DegreeEightCanonicalCatalogue.transitiveLiteralMatch published
    (preE7PairAction 4 p) (by norm_num)
    (Non2TransitiveActionClass.representative_not_isPGroup p.1.1)
  have F := canonicalFrame p M
  generalize h : M.index=j at F
  fin_cases j
  · exact ⟨FourPairCentralProductCanonicalRows.alternatingRowOfMatch p M h⟩
  · exact ⟨FourPairNormalChainCanonicalRows.s4RowOfMatch p M h⟩
  · exact False.elim (FourPairTop3NoPairing.no_frame F)
  · exact False.elim (FourPairTop4NoPairing.no_frame F)
  · exact False.elim (FourPairTop5NoPairing.no_frame F)
  · exact ⟨FourPairCentralProductCanonicalRows.symmetricRowOfMatch p M h⟩
  · exact False.elim (FourPairTop7NoPairing.no_frame F)
  · exact False.elim (FourPairTop8NoPairing.no_frame F)
  · exact False.elim (FourPairTop9NoPairing.no_frame F)
  · exact False.elim (FourPairTop10NoPairing.no_frame F)
  · exact ⟨FourPairNormalChainCanonicalRows.slRowOfMatch p M h⟩
  · exact ⟨FourPairY1CanonicalRow.rowOfMatch hZmud p M h⟩
  · exact ⟨FourPairY2CanonicalRow.rowOfMatch p M h⟩
  · exact ⟨FourPairNormalChainCanonicalRows.glRowOfMatch p M h⟩
  · exact ⟨FourPairY3CanonicalRow.rowOfMatch p M h⟩
  · exact ⟨FourPairY4CanonicalRow.rowOfMatch p M h⟩
  · exact ⟨FourPairY5CanonicalRow.rowOfMatch p M h⟩
  · exact False.elim (FourPairTop18NoPairing.no_frame F)
  · exact False.elim (FourPairTop19NoPairing.no_frame F)
  · exact False.elim (FourPairTop20NoPairing.no_frame F)
  · exact False.elim (FourPairTop21NoPairing.no_frame F)
  · exact False.elim (FourPairTop22NoPairing.no_frame F)
  · exact False.elim (FourPairTop23NoPairing.no_frame F)
  · exact False.elim (FourPairTop24NoPairing.no_frame F)

end SymmetricSubgroupAsymptotics.FourPairCanonicalClassification
end
