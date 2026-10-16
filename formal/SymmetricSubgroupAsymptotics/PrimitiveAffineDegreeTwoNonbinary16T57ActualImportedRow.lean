import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T57Physical
import SymmetricSubgroupAsymptotics.PreE7FiniteMixedPermutationStructural
import SymmetricSubgroupAsymptotics.OriginalSixteenPreE7Representative

/-! Actual preE7 semantic source for 16T57. The literal point action proves
membership, and the existing complete original-quotient certificates prove
the imported row; no supplied class-equivalence or completed row is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T57ActualImportedRow
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoNonbinary16T57AffineSocles (Original)

def chart : OriginalSixteenPreE7Representative.Chart Original :=
  OriginalSixteenPreE7Representative.choose Original
    PrimitiveAffineDegreeTwoNonbinary16T57Physical.nonbinary
    PrimitiveAffineDegreeTwoNonbinary16T57Physical.transitive

def index : PreE7NonPairActionClass 16 := chart.index

def originalEquiv : Original ≃* preE7NonPairAction 16 index := chart.groupEquiv

theorem actual_point_conjugacy :
    MulAut.conj chart.conjugator • Original = preE7NonPairAction 16 index :=
  chart.point_conjugacy

def importedRow (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) : DegreeTwoDegreeSixteenImportedRow index :=
  PreE7FiniteMixedPermutationMenu.importedRowOfEquiv hMN hZmud index originalEquiv
    (by decide : 2 ≤ 2)
    (fun N => by
      letI := N.2
      exact PrimitiveAffineDegreeTwoNonbinary16T57AffineSocles.quotientSocle N.1)

def source (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7RankTailSourceOrYonedaTopData 16 index :=
  (importedRow hMN hZmud).source

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T57ActualImportedRow
end
