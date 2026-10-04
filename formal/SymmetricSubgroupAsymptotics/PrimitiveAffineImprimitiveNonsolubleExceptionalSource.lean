import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveCoefficient
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallCatalogueCapacity

/-!
# Nonsoluble small affine exceptions are already component sources

The finite affine catalogue proves a uniform actual-wreath margin for every
nonsoluble primitive affine component of local degree eight or sixteen.
Those component-native results predate the exceptional-cell consumer, so
this file records the missing construction-facing adapter: transport their
complete source through the literal original block system.

Consequently all five numerical exception cells

* local degree eight with `2`, `4`, or `6` blocks; and
* local degree sixteen with `2` or `4` blocks

are closed whenever the literal affine complement is nonsoluble.  No
exceptional block count enters the proof; the resulting theorem is stronger
and can be used before the finite block-count split.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}

/-- A nonsoluble affine component of local degree eight or sixteen is an
ambient pre-`E₇` source on its original block system.  The local catalogue
supplies the component margin and the generic affine coefficient theorem
performs the literal ambient transfer. -/
noncomputable def degreeEightOrSixteenNonsolubleSource
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : FiniteSimpleTwoGeneratorBound)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hdegree : Nat.card block.Fibre = 8 ∨ Nat.card block.Fibre = 16)
    (hnonsolvable : ¬ IsSolvable (P.complement (origin block))) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let S : ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      block P := by
    rcases hdegree with h8 | h16
    · exact ComponentSource.of_degreeEight_nonsoluble hTraceyHalf
        hTraceyLog hTraceyRefined hTraceyPerm block P D h8 hnonsolvable
    · exact ComponentSource.of_degreeSixteen_nonsoluble hTraceyHalf
        hTraceyLog hTraceyRefined hTraceyPerm block P D h16 hnonsolvable
  exact imprimitiveAffineComponentTransfer hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm hgen block P S

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
