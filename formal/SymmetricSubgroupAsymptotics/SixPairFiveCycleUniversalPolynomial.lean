import SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalColumn0
import SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalColumn1
import SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalColumn2
import SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalColumn3
import SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalColumn4
import SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalColumn5
import SymmetricSubgroupAsymptotics.SixPairFiveCycleAllNormalB6

/-! The common five-cycle polynomial applies to EVERY mover of its unique
fixed point. Matrix data are therefore proved, rather than supplied per
stored action. The actual original correlated kernel is unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalPolynomial
open BinarySixPointFiveCyclePolynomial Non2UnipotentPrefixFiniteMenu

theorem matrix (q : Equiv.Perm (Fin 6)) (hq : q 5≠5) (i x : Fin 6) :
    actualOperator representation SixPointFiveCyclePrimitive.cycle q (Pi.single i 1) x=
      operator 0 (Pi.single i 1) x := by
  fin_cases i
  · exact column0 q hq x
  · exact column1 q hq x
  · exact column2 q hq x
  · exact column3 q hq x
  · exact column4 q hq x
  · exact column5 q hq x

def actionCertificate
    {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))
    (h6 : PublishedPrimitiveDegreeSixClassification) (hZmud : ZmudFaithfulCharacterTupleInput)
    (a b : U) (ha : F.top a=SixPointFiveCyclePrimitive.cycle) (hb : F.top b 5≠5) :
    PreE7B6ActionCertificate U :=
  SixPairFiveCycleAllNormalB6.actionCertificate F h6 hZmud a b (F.top b) ha rfl hb
    (matrix (F.top b) hb)

end SymmetricSubgroupAsymptotics.SixPairFiveCycleUniversalPolynomial
