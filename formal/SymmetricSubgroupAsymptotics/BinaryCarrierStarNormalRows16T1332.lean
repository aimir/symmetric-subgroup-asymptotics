import SymmetricSubgroupAsymptotics.BinaryCarrierAboveDerivedRows16
import SymmetricSubgroupAsymptotics.BinaryCarrierStarCrossingRows16T1332
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalRows16T1332
import SymmetricSubgroupAsymptotics.BinaryCarrierStarIntermediate16T1332

/-! Exhaustive row alternatives for every normal axis of the literal
original 16T1332 group. The four branches retain the actual containments
relative to D and R_D. Exact profiles are used in the two branches inside
D; the other branches retain their proved upper rows. No normal is
identified with a numerical label, and no weight or owner claim is made. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierStarNormalRows16T1332

open FullSubdirectGoursat JointCapacityRow BinaryCarrierAboveDerivedRows
open BinaryCarrierProfileRows

abbrev Original := BinaryCarrierAboveDerivedRows16T1332.Original
abbrev factor := BinaryCarrierAboveDerivedRows16T1332.factor
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D

theorem intermediate_actualRow_three_cases (N : NormalAxis Original)
    (hRN : R < N.1) (hND : N.1 < D) :
    BinaryCarrierWord.actualRow (A := factor) N = ⟨1,3,1,1,4,3⟩ ∨
    BinaryCarrierWord.actualRow (A := factor) N = ⟨2,4,2,1,4,2⟩ ∨
    BinaryCarrierWord.actualRow (A := factor) N = ⟨3,5,3,1,4,1⟩ := by
  have hp : PrimeDerivedOrderTwoProfiles.profile N.1 = (1,3,1,1,4,3) ∨
      PrimeDerivedOrderTwoProfiles.profile N.1 = (2,4,2,1,4,2) ∨
      PrimeDerivedOrderTwoProfiles.profile N.1 = (3,5,3,1,4,1) :=
    BinaryCarrierStarIntermediate16T1332.normal_profile N.1 hRN hND
  rcases hp with h | h | h
  · exact Or.inl (by simpa only [rowOfProfile, Nat.cast_one] using
      actualRow_eq_of_profile (A := factor) N (1,3,1,1,4,3) h)
  · exact Or.inr (Or.inl (by simpa only [rowOfProfile, Nat.cast_one] using
      actualRow_eq_of_profile (A := factor) N (2,4,2,1,4,2) h))
  · exact Or.inr (Or.inr (by simpa only [rowOfProfile, Nat.cast_one] using
      actualRow_eq_of_profile (A := factor) N (3,5,3,1,4,1) h))

/-- N=D belongs to the above-derived branch and N=R to the small branch.
The crossing bound is the already proved common upper box; neither its
head nor its order is asserted to equal the upper value. -/
theorem actualRow_coverage (N : NormalAxis Original) :
    (D ≤ N.1 ∧ imageDimension N.1 ≤ 5 ∧
      BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
        (row 6 5 4 (imageDimension N.1))) ∨
    (N.1 ≤ R ∧
      (BinaryCarrierWord.actualRow (A := factor) N = ⟨0,0,0,0,1,6⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨1,1,1,0,1,5⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨1,2,1,1,4,4⟩)) ∨
    (R < N.1 ∧ N.1 < D ∧
      (BinaryCarrierWord.actualRow (A := factor) N = ⟨1,3,1,1,4,3⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨2,4,2,1,4,2⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨3,5,3,1,4,1⟩)) ∨
    (¬N.1 ≤ D ∧ ¬D ≤ N.1 ∧
      BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
        BinaryCarrierStarEnvelope.coarseEnvelope) := by
  classical
  by_cases hDN : D ≤ N.1
  · exact Or.inl ⟨hDN, BinaryCarrierAboveDerivedRows16T1332.imageDimension_le_five N.1,
      BinaryCarrierAboveDerivedRows16T1332.actualRow_boundedBy N hDN⟩
  · apply Or.inr
    by_cases hND : N.1 ≤ D
    · by_cases hNR : N.1 ≤ R
      · exact Or.inl ⟨hNR, BinaryCarrierRadicalRows16T1332.actualRow_three_cases N hNR⟩
      · have hRN : R < N.1 := lt_of_le_not_ge
          ((BinaryCarrierRadicalSaturation16T1332.normal_comparable N.1 hND).resolve_left hNR) hNR
        have hND' : N.1 < D := lt_of_le_not_ge hND hDN
        exact Or.inr (Or.inl ⟨hRN, hND', intermediate_actualRow_three_cases N hRN hND'⟩)
    · exact Or.inr (Or.inr ⟨hND, hDN,
        BinaryCarrierStarCrossingRows16T1332.actualRow_boundedBy_coarse N hND hDN⟩)

end SymmetricSubgroupAsymptotics.BinaryCarrierStarNormalRows16T1332
