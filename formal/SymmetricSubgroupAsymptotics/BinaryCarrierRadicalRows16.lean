import SymmetricSubgroupAsymptotics.BinaryCarrierProfileRows
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1082
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1083
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1084
import SymmetricSubgroupAsymptotics.PrimeEvaluationKernelOrder

/-! Exact carrier rows for every original normal inside the order-two
derived relative radicals of 16T1082, 16T1083 and 16T1084. Each factor is
the literal original group. No normal enumeration or weight bound is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open FullSubdirectGoursat BinaryCarrierProfileRows

namespace BinaryCarrierRadicalRows16T1082

abbrev Original := BinaryCarrierRadicalProfiles16T1082.Original
abbrev R := primeRelativeRadical 2 (commutator Original)

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := isPGroup_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1082.evaluationKernel_eq_commutator 4
    (show Nat.card (commutator Original) = 2 ^ 4 from
      BinaryCarrierDerivedOrder16T1082.card_commutator)

theorem actualRow_two_cases (N : NormalAxis Original) (hN : N.1 ≤ R) :
    BinaryCarrierWord.actualRow (A := factor) N = ⟨0,0,0,0,1,4⟩ ∨
    BinaryCarrierWord.actualRow (A := factor) N = ⟨1,1,1,0,3,3⟩ := by
  simpa only [rowOfProfile, Nat.cast_one] using
    actualRow_two_cases_of_profile (A := factor) N (0,0,0,0,1,4) (1,1,1,0,3,3)
      (BinaryCarrierRadicalProfiles16T1082.normal_profile N.1 hN)

end BinaryCarrierRadicalRows16T1082

namespace BinaryCarrierRadicalRows16T1083

abbrev Original := BinaryCarrierRadicalProfiles16T1083.Original
abbrev R := primeRelativeRadical 2 (commutator Original)

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := isPGroup_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1083.evaluationKernel_eq_commutator 4
    (show Nat.card (commutator Original) = 2 ^ 4 from
      BinaryCarrierDerivedOrder16T1083.card_commutator)

theorem actualRow_two_cases (N : NormalAxis Original) (hN : N.1 ≤ R) :
    BinaryCarrierWord.actualRow (A := factor) N = ⟨0,0,0,0,1,4⟩ ∨
    BinaryCarrierWord.actualRow (A := factor) N = ⟨1,1,1,0,3,3⟩ := by
  simpa only [rowOfProfile, Nat.cast_one] using
    actualRow_two_cases_of_profile (A := factor) N (0,0,0,0,1,4) (1,1,1,0,3,3)
      (BinaryCarrierRadicalProfiles16T1083.normal_profile N.1 hN)

end BinaryCarrierRadicalRows16T1083

namespace BinaryCarrierRadicalRows16T1084

abbrev Original := BinaryCarrierRadicalProfiles16T1084.Original
abbrev R := primeRelativeRadical 2 (commutator Original)

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := isPGroup_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator 4
    (show Nat.card (commutator Original) = 2 ^ 4 from
      BinaryCarrierDerivedOrder16T1084.card_commutator)

theorem actualRow_two_cases (N : NormalAxis Original) (hN : N.1 ≤ R) :
    BinaryCarrierWord.actualRow (A := factor) N = ⟨0,0,0,0,1,4⟩ ∨
    BinaryCarrierWord.actualRow (A := factor) N = ⟨1,1,1,0,3,3⟩ := by
  simpa only [rowOfProfile, Nat.cast_one] using
    actualRow_two_cases_of_profile (A := factor) N (0,0,0,0,1,4) (1,1,1,0,3,3)
      (BinaryCarrierRadicalProfiles16T1084.normal_profile N.1 hN)

end BinaryCarrierRadicalRows16T1084

end SymmetricSubgroupAsymptotics
