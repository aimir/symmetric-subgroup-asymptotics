import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29GeneratedData
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29LocalSplitTable

/-!
# Degree-sixteen frame row 29 through the reusable table importer

This final wrapper binds the separately checked shared-top data, retained local
row, and split local-normal table to the generic degree-sixteen transport.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow29GeneratedTable

abbrev topData : GeneratedSixteenTopData :=
  PrimitiveAffineSixteenFrameRow29GeneratedData.topData

abbrev rowData : GeneratedSixteenRowData topData :=
  PrimitiveAffineSixteenFrameRow29GeneratedData.rowData

noncomputable def table : GeneratedSixteenTopTable topData :=
  PrimitiveAffineSixteenFrameRow29LocalSplitTable.table

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

noncomputable def bounds
    (pointEquiv : block.Points ≃ Fin 16)
    (conjugator : Equiv.Perm (Fin 16))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        topData.literalAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 :=
  GeneratedSixteenTopTable.bounds block P topData table pointEquiv conjugator
    hconjugated hr hD

end PrimitiveAffineSixteenFrameRow29GeneratedTable
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
