import SymmetricSubgroupAsymptotics.BinaryCarrierProfileRows
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1332
import SymmetricSubgroupAsymptotics.PrimeEvaluationKernelOrder

/-! The three proved small-radical profiles of 16T1332 are exact rows
for every original normal axis inside R_D. The original group and normal
axis remain unchanged, without a normal catalogue or weight assumption. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRadicalRows16T1332

open FullSubdirectGoursat BinaryCarrierProfileRows

abbrev Original := BinaryCarrierRadicalProfiles16T1332.Original
abbrev R := primeRelativeRadical 2 (commutator Original)

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := isPGroup_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator 6
    (show Nat.card (commutator Original) = 2 ^ 6 from
      BinaryCarrierDerivedOrder16T1332.card_commutator)

theorem actualRow_eq_profile (N : NormalAxis Original) :
    BinaryCarrierWord.actualRow (A := factor) N =
      rowOfProfile (BinaryCarrierRadicalProfiles16T1332.profile N.1) := rfl

theorem actualRow_three_cases (N : NormalAxis Original) (hN : N.1 ≤ R) :
    BinaryCarrierWord.actualRow (A := factor) N = ⟨0,0,0,0,1,6⟩ ∨
    BinaryCarrierWord.actualRow (A := factor) N = ⟨1,1,1,0,1,5⟩ ∨
    BinaryCarrierWord.actualRow (A := factor) N = ⟨1,2,1,1,4,4⟩ := by
  rw [actualRow_eq_profile]
  rcases BinaryCarrierRadicalProfiles16T1332.normal_profile N.1 hN with h | h | h
  · exact Or.inl (by simpa only [rowOfProfile, Nat.cast_one] using congrArg rowOfProfile h)
  · exact Or.inr (Or.inl (by
      simpa only [rowOfProfile, Nat.cast_one] using congrArg rowOfProfile h))
  · exact Or.inr (Or.inr (by
      simpa only [rowOfProfile, Nat.cast_one] using congrArg rowOfProfile h))

end SymmetricSubgroupAsymptotics.BinaryCarrierRadicalRows16T1332
