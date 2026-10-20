import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairGeneralSourceAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCharacterOnlySource

/-! Reuse an already checked original twelve-point quotient-socle profile
at kappa ONE as a complete six-pair source. Only the actual group
isomorphism is transported; no width24 source or historical family label
is treated as a width12 source. The natural-module field is unnecessary. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairSourceOfTwelveSocleOneProfile
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable (D : DegreeTwoPairTopFiniteInterface 12)
  (C : D.normalRegistry.QuotientSocleGeneratorFamily 1)
  (p : PreE7PairActionClass 6)
  (e : D.top ≃* preE7PairAction 6 p)
  (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))

private def registry := D.normalRegistry.mapEquiv e
private def family : (registry D p e).QuotientSocleGeneratorFamily 1 where
  data j := (C.data j).mapEquiv e

/-- All normal axes are recovered through the checked registry equivalence. -/
def actionCertificate (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7B6ActionCertificate (preE7PairAction 6 p) :=
  (PreE7B6CharacterOnlyQuotientData.ofOneGeneral hZmud (fun N =>
    FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.dispatch
      (registry D p e) (family D C p e) N)).toB6ActionCertificate F

/-- Exact actual-action source from a proved kappa-one finite profile. -/
def source (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  .inl (.b6 (actionCertificate D C p e F hZmud))

end SymmetricSubgroupAsymptotics.SixPairSourceOfTwelveSocleOneProfile
