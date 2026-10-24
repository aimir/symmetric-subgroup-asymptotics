import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveDerived
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedGoodSylow

/-! Unconditional good-Sylow data on the same original derived/full-centre
Ree model for m>0. The field-order-two Tits model is separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalGoodSylow

theorem original_goodSylowPrime (m : ℕ) (hm : 0 < m) :
    CFSGReduction.GoodSylowPrime (CFSG.Models.ReeF4 m) 2 :=
  CFSGReeFFourFixedGoodSylow.original_goodSylowPrime_of_positive_le m
    (CFSGReeFFourPositiveDerived.fixedPositive_le_commutator m hm)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalGoodSylow
