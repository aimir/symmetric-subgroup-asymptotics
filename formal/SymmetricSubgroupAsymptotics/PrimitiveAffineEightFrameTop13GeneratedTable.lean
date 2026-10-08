import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop13LocalNormalTable

/-!
# Rows 22 through one generated top table

The rows share their Cayley model, point stabilizer, conjugacy cover and
complete normal-subgroup catalogue.  The local quotient is selected by the
checked table before the generic induced-module transport is applied.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameTop13GeneratedTable

abbrev topData := PrimitiveAffineEightFrameTop13GeneratedData.topData

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The complete finite-frame bound for every row over this literal top. -/
noncomputable def bounds
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        topData.literalAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 :=
  GeneratedTopTable.bounds block P topData PrimitiveAffineEightFrameTop13LocalNormalTable.table
    pointEquiv conjugator hconjugated hr hD hs

end PrimitiveAffineEightFrameTop13GeneratedTable
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
