import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T1932Physical
import SymmetricSubgroupAsymptotics.OriginalSixteenPreE7Representative
import SymmetricSubgroupAsymptotics.PreE7FiniteMixedPermutationStructural

/-! Genuine actual preE7 imported row for16T1932. The selected point words
and cubic element prove its physical class membership; the checked generic
permutation importer consumes its actual all-quotient socle bound. No order
cutoff, finite normal census or unproved class binding is an input. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T1932ActualImportedRow
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles (Original)

def chart : OriginalSixteenPreE7Representative.Chart Original :=
  OriginalSixteenPreE7Representative.choose Original
    PrimitiveAffineDegreeTwoNonbinary16T1932Physical.nonbinary
    PrimitiveAffineDegreeTwoNonbinary16T1932Physical.transitive

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
      exact PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.quotientSocle N.1)

def source (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) : PreE7RankTailSourceOrYonedaTopData 16 index :=
  (importedRow hMN hZmud).source

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T1932ActualImportedRow
end
