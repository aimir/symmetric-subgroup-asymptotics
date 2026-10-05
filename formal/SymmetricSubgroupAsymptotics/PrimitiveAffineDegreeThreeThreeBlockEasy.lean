import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientEndpoint
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoThreePairsEasySource

/-!
# The pointwise signed-quotient model at three blocks

Among the published three-pair quotient models, only the natural `S3` model
fits the pointwise identity-comparator margin after a ternary layer is
prepended.  The ambient degree is nine and `evenWidth 9 = 8`; hence generic
capacity one leaves room for comparator degree three, but not degree four or
five.  The other models must retain their additive or source-summed estimates
and are deliberately absent from this file.
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

/-- Literal recognition of the sole pointwise three-block quotient row. -/
structure DegreeThreeThreeBlockPointwiseModel : Type where
  equiv : (preE7NonPairAction w U ⧸ E block P) ≃*
    Equiv.Perm (Fin 3)

namespace DegreeThreeThreeBlockPointwiseModel

/-- The natural `S3` quotient closes the original ternary action after the
literal translation layer is prepended. -/
noncomputable def source
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 3)
    (M : DegreeThreeThreeBlockPointwiseModel block P) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  degreeThreeThreeBlocksIdentitySource block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm hr hs 3 M.equiv.toMonoidHom M.equiv.injective
    (by norm_num) (by norm_num)

end DegreeThreeThreeBlockPointwiseModel

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
