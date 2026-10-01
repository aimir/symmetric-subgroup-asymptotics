import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure
import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceComparator

/-!
# Complete-source witnesses at the T1 structural boundary

The structural exhaustion theorem should return the correlated certificate it
actually proves.  This module sends either semisimple complete-source record
straight to the ordinary sector of the rank-tail catalogue.  No conversion
to a pointwise normal-axis estimate occurs on this path.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A semisimple quotient comparator is already a concrete owner source at
the final T1 exhaustion boundary. -/
noncomputable def PreE7SemisimpleCompleteSourceData.toRankTailOwnerSource
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (D : PreE7SemisimpleCompleteSourceData family w i) :
    PreE7RankTailOwnerSourceData w i :=
  .ordinary family (.completeSource D.numericalData)

/-- The variant whose quotient moment and outer factor were bounded together
also enters the final catalogue without weakening its complete-source bound. -/
noncomputable def
    PreE7SemisimpleDirectCompleteSourceData.toRankTailOwnerSource
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (D : PreE7SemisimpleDirectCompleteSourceData family w i) :
    PreE7RankTailOwnerSourceData w i :=
  .ordinary family (.completeSource D.numericalData)

/-- Any already assembled direct complete-source numerical certificate is a
literal ordinary owner source for the final rank-tail catalogue. -/
noncomputable def PreE7CompleteSourceNumericalData.toRankTailOwnerSource
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (D : PreE7CompleteSourceNumericalData family w i) :
    PreE7RankTailOwnerSourceData w i :=
  .ordinary family (.completeSource D)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
