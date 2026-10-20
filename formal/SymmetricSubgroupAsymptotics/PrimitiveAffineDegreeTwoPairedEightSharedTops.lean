import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineLiteralTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightNaturalTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopCatalogues
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop1
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop2
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop3
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop4
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop5
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop6
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop7
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop11
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop12
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop14
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop19
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop21
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop22
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop8
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop9
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop10
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop13
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop15
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop16
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightTop17

/-!
# Reuse of the twenty-four degree-eight pair tops

The count-sixteen paired branch uses the twenty-four transitive groups of
degree eight.  Twenty of these tops already occur in the degree-four
shared-top proof.  This file reuses their checked Cayley/normal-word data
directly and installs the actual natural eight-coordinate permutation
module.  The four tops excluded by the older local-quotient eligibility
condition are supplied semantically: the two affine literal actions are
given by their pinned generators, and the final two are natural `A_8` and
`S_8`.

Thus `interface` is a concrete `Fin 24` family of complete pair-top
interfaces.  No normal or module census flag is assumed.  The remaining
row work is the profile/relative-character theorem on these interfaces.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

/-- The complete ordered family `paired8-1` through `paired8-24`. -/
noncomputable def interface : Fin 24 → DegreeTwoPairTopFiniteInterface 8 :=
  Fin.cases top1 <| Fin.cases top2 <| Fin.cases top3 <| Fin.cases top4 <|
  Fin.cases top5 <| Fin.cases top6 <| Fin.cases top7 <| Fin.cases top8 <|
  Fin.cases top9 <| Fin.cases top10 <| Fin.cases top11 <| Fin.cases top12 <|
  Fin.cases top13 <| Fin.cases top14 <| Fin.cases top15 <| Fin.cases top16 <|
  Fin.cases top17 <| Fin.cases top18 <| Fin.cases top19 <| Fin.cases top20 <|
  Fin.cases top21 <| Fin.cases top22 <| Fin.cases top23 <|
  Fin.cases top24 Fin.elim0

/-- Fill the paired-eight field of the count-sixteen catalogue with the
reused complete interfaces.  Only the three genuinely degree-sixteen
families remain to be supplied by the width-16 producer. -/
noncomputable def sixteenCatalogue
    (zero16 : Fin 29 → DegreeTwoPairTopFiniteInterface 16)
    (twoAffine16 : Fin 15 → DegreeTwoPairTopFiniteInterface 16)
    (primitive16 : Fin 20 → DegreeTwoPairTopFiniteInterface 16) :
    DegreeTwoSixteenPairTopFiniteCatalogue where
  paired8 := interface
  zero16 := zero16
  twoAffine16 := twoAffine16
  primitive16 := primitive16

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
