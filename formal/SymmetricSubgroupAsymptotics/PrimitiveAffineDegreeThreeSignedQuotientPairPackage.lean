import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientPairFrame
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRawExceptionalGrowth

/-!
# Pulling a literal pair package back to the signed quotient

The degree-two finite slices produce their raw estimates on the literal
permutation range of the signed quotient.  The source used by the ternary
prepend, however, is the quotient group itself.  This file records the
single exact transport between them.  It keeps the actual block system,
the pair frame, the retained comparator, and the raw exceptional growth;
there is no action-class replacement and no owner-order premise.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Transport a raw pair package on the literal relabelled range back to
the exact signed quotient `U / E`.  The comparator action and every
coefficient are unchanged. -/
noncomputable def DegreeThreeSignedQuotientPairChart.pullbackGrowthPackage
    {s : ℕ} (C : DegreeThreeSignedQuotientPairChart block P s)
    (G : PreE7DegreeTwoPairQuotientGrowthPackage C.action) :
    PreE7DegreeTwoPairQuotientGrowthPackage
      (preE7NonPairAction w U ⧸ E block P) :=
  G.comapEquiv C.sourceEquiv

/-- The corresponding raw summed envelope, stated separately for callers
which do not need the exceptional-growth certificate. -/
noncomputable def DegreeThreeSignedQuotientPairChart.pullbackSummedPackage
    {s : ℕ} (C : DegreeThreeSignedQuotientPairChart block P s)
    (S : PreE7DegreeTwoPairQuotientSummedPackage C.action) :
    PreE7DegreeTwoPairQuotientSummedPackage
      (preE7NonPairAction w U ⧸ E block P) :=
  S.comapEquiv C.sourceEquiv

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
