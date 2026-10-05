import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientPairPackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientNonbinary
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientKernel
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsGrowthPackage

/-!
# The literal four-pair package of a degree-three affine component

This is the exact structural dispatcher before the ambient numerical row.
It retains the actual signed quotient and pair frame.  In the nonbinary
branch, the published degree-eight pair correspondence supplies its raw
growth package; the binary branch remains visible together with its proven
nonzero pair kernel.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Fixed four-pair chart on the actual signed quotient. -/
noncomputable def degreeThreeFourBlockPairChart
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    DegreeThreeSignedQuotientPairChart block P 4 :=
  degreeThreeSignedQuotientPairChart block P hr hs hcomponent

/-- The published nonbinary four-pair package, pulled back to the literal
signed quotient `U/E`. -/
noncomputable def degreeThreeFourBlockNonbinaryGrowthPackage
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hnonbinary : ¬ IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    PreE7DegreeTwoPairQuotientGrowthPackage
      (preE7NonPairAction w U ⧸ E block P) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let G := degreeTwoFourPairLiteralGrowthPackage hZmud lit published
    C.action hnonbinary C.pretransitive C.frame
  exact C.pullbackGrowthPackage block P G

/-- In the complementary binary branch, the frame supplied to the binary
normal-axis theorem has the actual nonzero signed block kernel. -/
theorem degreeThreeFourBlockBinaryFrame_kernel_ne_bot
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hK : degreeNineLinearBlockKernel block P ≠ ⊥) :
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).frame.top.ker ≠
      ⊥ :=
  degreeThreeSignedQuotientPairChart_frame_top_ker_ne_bot
    block P hr hs hcomponent hK

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
