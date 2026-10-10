import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10GeneratedData
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10LocalSplitTable

/-! Generated final transport wrapper for one degree-sixteen frame row. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow10GeneratedTable

abbrev topData : GeneratedSixteenTopData :=
  PrimitiveAffineSixteenFrameRow10GeneratedData.topData

abbrev rowData : GeneratedSixteenRowData topData :=
  PrimitiveAffineSixteenFrameRow10GeneratedData.rowData

noncomputable def table : GeneratedSixteenTopTable topData :=
  PrimitiveAffineSixteenFrameRow10LocalSplitTable.table

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

end PrimitiveAffineSixteenFrameRow10GeneratedTable
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
