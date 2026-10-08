import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop8LocalNormalTable

/-!
# Rows 10--13 through one generated top table

The four catalogue rows over transitive top 8 share their Cayley model,
point stabilizer, conjugacy cover and complete normal-subgroup catalogue.
`PrimitiveAffineEightFrameTop8LocalNormalTable.table` retains the four
row-varying local quotients and binary modules.  The public bound below is
therefore a single application of the generic generated-row transport.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameTop8GeneratedTable

abbrev topData := PrimitiveAffineEightFrameTop8GeneratedData.topData

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The complete finite-frame bound for every row over transitive top 8.
The local quotient is selected internally by the checked normal catalogue. -/
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
  GeneratedTopTable.bounds block P topData
    PrimitiveAffineEightFrameTop8LocalNormalTable.table
    pointEquiv conjugator hconjugated hr hD hs

end PrimitiveAffineEightFrameTop8GeneratedTable
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
