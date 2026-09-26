import SymmetricSubgroupAsymptotics.BinaryCarrierAboveDerivedRows16
import SymmetricSubgroupAsymptotics.BinaryCarrierCrossingRows16
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalRows16
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalRows16T1547
import SymmetricSubgroupAsymptotics.BinaryCarrierPairIntermediate16T1082
import SymmetricSubgroupAsymptotics.BinaryCarrierPairIntermediate16T1083
import SymmetricSubgroupAsymptotics.BinaryCarrierPairIntermediate16T1084
import SymmetricSubgroupAsymptotics.BinaryCarrierPairIntermediate16T1547

/-! Exhaustive row alternatives for every original normal axis of the
four pair-family masters. The split retains the actual containments:
above D; inside R; strictly between R and D; or crossing D. Saturation
proves comparability only in the branch inside D. The original normal
axis is never replaced by a row label, and no weight or owner assertion
or count of normals follows from these alternatives. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open FullSubdirectGoursat JointCapacityRow BinaryCarrierAboveDerivedRows
open BinaryCarrierProfileRows

namespace BinaryCarrierPairNormalRows16T1082

abbrev Original := BinaryCarrierAboveDerivedRows16T1082.Original
abbrev factor := BinaryCarrierAboveDerivedRows16T1082.factor
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D

theorem intermediate_actualRow_two_cases (N : NormalAxis Original)
    (hRN : R < N.1) (hND : N.1 < D) :
    BinaryCarrierWord.actualRow (A := factor) N = ⟨1,2,1,1,2,2⟩ ∨
      BinaryCarrierWord.actualRow (A := factor) N = ⟨2,3,2,1,3,1⟩ := by
  simpa only [rowOfProfile, Nat.cast_one] using
    actualRow_two_cases_of_profile (A := factor) N (1,2,1,1,2,2) (2,3,2,1,3,1)
      (BinaryCarrierPairIntermediate16T1082.normal_profile N.1 hRN hND)

/-- N=D is assigned to the first branch and N=R to the second.
Different original normals with the same row remain different inputs. -/
theorem actualRow_coverage (N : NormalAxis Original) :
    (D ≤ N.1 ∧ imageDimension N.1 ≤ 6 ∧
      BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
        (row 4 6 3 (imageDimension N.1))) ∨
    (N.1 ≤ R ∧
      (BinaryCarrierWord.actualRow (A := factor) N = ⟨0,0,0,0,1,4⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨1,1,1,0,3,3⟩)) ∨
    (R < N.1 ∧ N.1 < D ∧
      (BinaryCarrierWord.actualRow (A := factor) N = ⟨1,2,1,1,2,2⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨2,3,2,1,3,1⟩)) ∨
    (¬N.1 ≤ D ∧ ¬D ≤ N.1 ∧
      (BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 3 1 ∨
       BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 3 2)) := by
  classical
  by_cases hDN : D ≤ N.1
  · exact Or.inl ⟨hDN, BinaryCarrierAboveDerivedRows16T1082.imageDimension_le_six N.1,
      BinaryCarrierAboveDerivedRows16T1082.actualRow_boundedBy N hDN⟩
  · apply Or.inr
    by_cases hND : N.1 ≤ D
    · by_cases hNR : N.1 ≤ R
      · exact Or.inl ⟨hNR, BinaryCarrierRadicalRows16T1082.actualRow_two_cases N hNR⟩
      · have hRN : R < N.1 := lt_of_le_not_ge
          ((BinaryCarrierRadicalSaturation16T1082.normal_comparable N.1 hND).resolve_left hNR) hNR
        have hND' : N.1 < D := lt_of_le_not_ge hND hDN
        exact Or.inr (Or.inl ⟨hRN, hND', intermediate_actualRow_two_cases N hRN hND'⟩)
    · exact Or.inr (Or.inr ⟨hND, hDN,
        BinaryCarrierCrossingRows16T1082.actualRow_two_cases N hND hDN⟩)

end BinaryCarrierPairNormalRows16T1082

namespace BinaryCarrierPairNormalRows16T1083

abbrev Original := BinaryCarrierAboveDerivedRows16T1083.Original
abbrev factor := BinaryCarrierAboveDerivedRows16T1083.factor
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D

theorem intermediate_actualRow_two_cases (N : NormalAxis Original)
    (hRN : R < N.1) (hND : N.1 < D) :
    BinaryCarrierWord.actualRow (A := factor) N = ⟨1,2,1,1,2,2⟩ ∨
      BinaryCarrierWord.actualRow (A := factor) N = ⟨2,3,2,1,3,1⟩ := by
  simpa only [rowOfProfile, Nat.cast_one] using
    actualRow_two_cases_of_profile (A := factor) N (1,2,1,1,2,2) (2,3,2,1,3,1)
      (BinaryCarrierPairIntermediate16T1083.normal_profile N.1 hRN hND)

theorem actualRow_coverage (N : NormalAxis Original) :
    (D ≤ N.1 ∧ imageDimension N.1 ≤ 6 ∧
      BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
        (row 4 6 3 (imageDimension N.1))) ∨
    (N.1 ≤ R ∧
      (BinaryCarrierWord.actualRow (A := factor) N = ⟨0,0,0,0,1,4⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨1,1,1,0,3,3⟩)) ∨
    (R < N.1 ∧ N.1 < D ∧
      (BinaryCarrierWord.actualRow (A := factor) N = ⟨1,2,1,1,2,2⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨2,3,2,1,3,1⟩)) ∨
    (¬N.1 ≤ D ∧ ¬D ≤ N.1 ∧
      (BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 3 1 ∨
       BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 3 2)) := by
  classical
  by_cases hDN : D ≤ N.1
  · exact Or.inl ⟨hDN, BinaryCarrierAboveDerivedRows16T1083.imageDimension_le_six N.1,
      BinaryCarrierAboveDerivedRows16T1083.actualRow_boundedBy N hDN⟩
  · apply Or.inr
    by_cases hND : N.1 ≤ D
    · by_cases hNR : N.1 ≤ R
      · exact Or.inl ⟨hNR, BinaryCarrierRadicalRows16T1083.actualRow_two_cases N hNR⟩
      · have hRN : R < N.1 := lt_of_le_not_ge
          ((BinaryCarrierRadicalSaturation16T1083.normal_comparable N.1 hND).resolve_left hNR) hNR
        have hND' : N.1 < D := lt_of_le_not_ge hND hDN
        exact Or.inr (Or.inl ⟨hRN, hND', intermediate_actualRow_two_cases N hRN hND'⟩)
    · exact Or.inr (Or.inr ⟨hND, hDN,
        BinaryCarrierCrossingRows16T1083.actualRow_two_cases N hND hDN⟩)

end BinaryCarrierPairNormalRows16T1083

namespace BinaryCarrierPairNormalRows16T1084

abbrev Original := BinaryCarrierAboveDerivedRows16T1084.Original
abbrev factor := BinaryCarrierAboveDerivedRows16T1084.factor
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D

theorem intermediate_actualRow_two_cases (N : NormalAxis Original)
    (hRN : R < N.1) (hND : N.1 < D) :
    BinaryCarrierWord.actualRow (A := factor) N = ⟨1,2,1,1,2,2⟩ ∨
      BinaryCarrierWord.actualRow (A := factor) N = ⟨2,3,2,1,3,1⟩ := by
  simpa only [rowOfProfile, Nat.cast_one] using
    actualRow_two_cases_of_profile (A := factor) N (1,2,1,1,2,2) (2,3,2,1,3,1)
      (BinaryCarrierPairIntermediate16T1084.normal_profile N.1 hRN hND)

theorem actualRow_coverage (N : NormalAxis Original) :
    (D ≤ N.1 ∧ imageDimension N.1 ≤ 6 ∧
      BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
        (row 4 6 3 (imageDimension N.1))) ∨
    (N.1 ≤ R ∧
      (BinaryCarrierWord.actualRow (A := factor) N = ⟨0,0,0,0,1,4⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨1,1,1,0,3,3⟩)) ∨
    (R < N.1 ∧ N.1 < D ∧
      (BinaryCarrierWord.actualRow (A := factor) N = ⟨1,2,1,1,2,2⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨2,3,2,1,3,1⟩)) ∨
    (¬N.1 ≤ D ∧ ¬D ≤ N.1 ∧
      (BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 3 1 ∨
       BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 3 2)) := by
  classical
  by_cases hDN : D ≤ N.1
  · exact Or.inl ⟨hDN, BinaryCarrierAboveDerivedRows16T1084.imageDimension_le_six N.1,
      BinaryCarrierAboveDerivedRows16T1084.actualRow_boundedBy N hDN⟩
  · apply Or.inr
    by_cases hND : N.1 ≤ D
    · by_cases hNR : N.1 ≤ R
      · exact Or.inl ⟨hNR, BinaryCarrierRadicalRows16T1084.actualRow_two_cases N hNR⟩
      · have hRN : R < N.1 := lt_of_le_not_ge
          ((BinaryCarrierRadicalSaturation16T1084.normal_comparable N.1 hND).resolve_left hNR) hNR
        have hND' : N.1 < D := lt_of_le_not_ge hND hDN
        exact Or.inr (Or.inl ⟨hRN, hND', intermediate_actualRow_two_cases N hRN hND'⟩)
    · exact Or.inr (Or.inr ⟨hND, hDN,
        BinaryCarrierCrossingRows16T1084.actualRow_two_cases N hND hDN⟩)

end BinaryCarrierPairNormalRows16T1084

namespace BinaryCarrierPairNormalRows16T1547

abbrev Original := BinaryCarrierAboveDerivedRows16T1547.Original
abbrev factor := BinaryCarrierAboveDerivedRows16T1547.factor
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D

theorem intermediate_actualRow_two_cases (N : NormalAxis Original)
    (hRN : R < N.1) (hND : N.1 < D) :
    BinaryCarrierWord.actualRow (A := factor) N = ⟨1,4,2,2,2,2⟩ ∨
      BinaryCarrierWord.actualRow (A := factor) N = ⟨2,5,2,2,3,1⟩ := by
  simpa only [rowOfProfile, Nat.cast_one] using
    actualRow_two_cases_of_profile (A := factor) N (1,4,2,2,2,2) (2,5,2,2,3,1)
      (BinaryCarrierPairIntermediate16T1547.normal_profile N.1 hRN hND)

theorem actualRow_coverage (N : NormalAxis Original) :
    (D ≤ N.1 ∧ imageDimension N.1 ≤ 6 ∧
      BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
        (row 6 6 3 (imageDimension N.1))) ∨
    (N.1 ≤ R ∧
      (BinaryCarrierWord.actualRow (A := factor) N = ⟨0,0,0,0,1,6⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨1,1,1,0,2,5⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨1,2,1,1,1,4⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨2,3,2,1,3,3⟩)) ∨
    (R < N.1 ∧ N.1 < D ∧
      (BinaryCarrierWord.actualRow (A := factor) N = ⟨1,4,2,2,2,2⟩ ∨
       BinaryCarrierWord.actualRow (A := factor) N = ⟨2,5,2,2,3,1⟩)) ∨
    (¬N.1 ≤ D ∧ ¬D ≤ N.1 ∧
      (BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 5 1 ∨
       BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 5 2)) := by
  classical
  by_cases hDN : D ≤ N.1
  · exact Or.inl ⟨hDN, BinaryCarrierAboveDerivedRows16T1547.imageDimension_le_six N.1,
      BinaryCarrierAboveDerivedRows16T1547.actualRow_boundedBy N hDN⟩
  · apply Or.inr
    by_cases hND : N.1 ≤ D
    · by_cases hNR : N.1 ≤ R
      · exact Or.inl ⟨hNR, BinaryCarrierRadicalRows16T1547.actualRow_four_cases N hNR⟩
      · have hRN : R < N.1 := lt_of_le_not_ge
          ((BinaryCarrierRadicalSaturation16T1547.normal_comparable N.1 hND).resolve_left hNR) hNR
        have hND' : N.1 < D := lt_of_le_not_ge hND hDN
        exact Or.inr (Or.inl ⟨hRN, hND', intermediate_actualRow_two_cases N hRN hND'⟩)
    · exact Or.inr (Or.inr ⟨hND, hDN,
        BinaryCarrierCrossingRows16T1547.actualRow_two_cases N hND hDN⟩)

end BinaryCarrierPairNormalRows16T1547

end SymmetricSubgroupAsymptotics
