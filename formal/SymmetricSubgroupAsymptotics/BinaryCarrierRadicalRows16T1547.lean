import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1547
import SymmetricSubgroupAsymptotics.BinaryCarrierWordHistory
import SymmetricSubgroupAsymptotics.PrimeEvaluationKernelOrder

/-! The four proved small-radical profiles are the actual carrier rows
of every original normal axis contained in R_D. This bridge preserves the
literal original factor and every normal axis, including different axes
having the same row. It asserts no weight or all-normal coverage bound. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRadicalRows16T1547

open FullSubdirectGoursat BinaryMarkedGoursatPeel

abbrev Original := BinaryCarrierRadicalProfiles16T1547.Original
abbrev R := primeRelativeRadical 2 (commutator Original)

/-- A narrow factor for the SAME literal original closure. Its binary
property follows from the checked actual derived order and evaluation
kernel, without importing the other four concrete masters. -/
def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := isPGroup_of_evaluationKernel_eq 2
    BinaryCarrierDerived16T1547.evaluationKernel_eq_commutator 6
    (show Nat.card (commutator Original) = 2 ^ 6 from
      BinaryCarrierDerivedOrder16T1547.card_commutator)

def rowOfProfile (v : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : JointCapacityRow :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, (v.2.2.2.2.1 : ℝ), (v.2.2.2.2.2 : ℝ)⟩

theorem actualRow_eq_profile (N : NormalAxis Original) :
    BinaryCarrierWord.actualRow (A := factor) N =
      rowOfProfile (BinaryCarrierRadicalProfiles16T1547.profile N.1) := rfl

/-- These are alternatives for every original normal inside R, not a
list of original subgroups and not a claim that each row is realized. -/
theorem actualRow_four_cases (N : NormalAxis Original) (hN : N.1 ≤ R) :
    BinaryCarrierWord.actualRow (A := factor) N = ⟨0,0,0,0,1,6⟩ ∨
    BinaryCarrierWord.actualRow (A := factor) N = ⟨1,1,1,0,2,5⟩ ∨
    BinaryCarrierWord.actualRow (A := factor) N = ⟨1,2,1,1,1,4⟩ ∨
    BinaryCarrierWord.actualRow (A := factor) N = ⟨2,3,2,1,3,3⟩ := by
  rw [actualRow_eq_profile]
  rcases BinaryCarrierRadicalProfiles16T1547.normal_profile N.1 hN with h | h | h | h
  · exact Or.inl (by simpa only [rowOfProfile, Nat.cast_one] using congrArg rowOfProfile h)
  · exact Or.inr (Or.inl (by
      simpa only [rowOfProfile, Nat.cast_one] using congrArg rowOfProfile h))
  · exact Or.inr (Or.inr (Or.inl (by
      simpa only [rowOfProfile, Nat.cast_one] using congrArg rowOfProfile h)))
  · exact Or.inr (Or.inr (Or.inr (by
      simpa only [rowOfProfile, Nat.cast_one] using congrArg rowOfProfile h)))

end SymmetricSubgroupAsymptotics.BinaryCarrierRadicalRows16T1547
