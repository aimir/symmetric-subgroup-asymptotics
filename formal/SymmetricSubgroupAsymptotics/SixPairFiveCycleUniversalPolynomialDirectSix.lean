import SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalPolynomial
import SymmetricSubgroupAsymptotics.SixPairFiveCycleAllNormalB6DirectSix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalPolynomial.DirectSix
open BinarySixPointFiveCyclePolynomial Non2UnipotentPrefixFiniteMenu

def actionCertificate
    {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) (hZmud : ZmudFaithfulCharacterTupleInput)
    (a b : U) (ha : F.top a=SixPointFiveCyclePrimitive.cycle) (hb : F.top b 5≠5) :
    PreE7B6ActionCertificate U :=
  SixPairFiveCycleAllNormalB6.DirectSix.actionCertificate F hindex hZmud a b (F.top b) ha rfl hb
    (matrix (F.top b) hb)


end SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalPolynomial.DirectSix
