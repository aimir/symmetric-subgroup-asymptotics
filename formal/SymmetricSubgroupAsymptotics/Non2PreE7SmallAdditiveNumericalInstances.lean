import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveBasicNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveRecoveredNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7SaprimDegreeFive
import SymmetricSubgroupAsymptotics.Non2PreE7SaprimBinaryAffine
import SymmetricSubgroupAsymptotics.Non2PreE7SaprimOddCyclicAffine
import SymmetricSubgroupAsymptotics.Non2PreE7SaprimOddLargeAffine
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure

/-!
# Completed small additive sources in the T1 owner infrastructure

This is the source-facing dispatcher for every small fixed-degree owner whose
local group theory and finite menu totals are complete.  Each constructor
retains the actual action predicate.  The dispatcher produces first the
ordinary numerical package and then the rank-tail owner source used by the
final T1 action exhaustion.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The six small-family action predicates whose complete numerical owner
packages are currently proved.  All other family fibres are empty. -/
def PreE7CompletedSmallOwnerSourceData :
    PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Type
  | .dih => fun w i => PreE7DihSource w i
  | .s4 => fun w i => PLift (PreE7S4Source w i)
  | .a4w2 => fun w i => PreE7A4W2Source w i
  | .lin => fun w i => PreE7LinSource w i
  | .saprim => fun w i =>
      PreE7SaprimRegularPrimeSource w i ⊕
        (PreE7SaprimDegreeFiveSource w i ⊕
          (PreE7SaprimBinaryAffineSource w i ⊕
            (PreE7SaprimOddCyclicAffineSource w i ⊕
              PreE7SaprimOddLargeAffineSource w i)))
  | .tf => fun w i => PreE7TFSource w i
  | _ => fun _ _ => PEmpty

/-- Every completed small action supplies the exact numerical data expected
by the ordinary owner package. -/
noncomputable def PreE7CompletedSmallOwnerSourceData.numericalData
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : PreE7CompletedSmallOwnerSourceData family w i) :
    PreE7SmallAdditiveNumericalData family w i := by
  cases family
  all_goals first
    | exact PEmpty.elim S
    | skip
  case dih => exact PreE7DihSource.numericalData S hKP
  case s4 => exact preE7_s4_numericalData w i S.down
  case a4w2 => exact preE7_a4w2_numericalData w i S
  case lin => exact preE7_lin_numericalData w i S
  case saprim =>
    rcases S with S | S
    · exact PreE7SaprimRegularPrimeSource.numericalData S hKP
    · rcases S with S | S
      · exact S.numericalData
      · rcases S with S | S
        · exact S.numericalData
        · rcases S with S | S
          · exact S.numericalData hKP
          · exact S.numericalData hgen
  case tf => exact preE7_tf_numericalData w i S

/-- A completed small action as an ordinary numerical source. -/
noncomputable def PreE7CompletedSmallOwnerSourceData.toOrdinarySource
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : PreE7CompletedSmallOwnerSourceData family w i) :
    PreE7OrdinaryNumericalSourceData family w i :=
  .small (S.numericalData hgen hKP family)

/-- A completed small action in the concrete owner sum used by T1. -/
noncomputable def PreE7CompletedSmallOwnerSourceData.toRankTailOwnerSource
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : PreE7CompletedSmallOwnerSourceData family w i) :
    PreE7RankTailOwnerSourceData w i :=
  .ordinary family (S.toOrdinarySource hgen hKP family)

/-- The six completed small predicates enter the exact numerical earlier
family predicate, with no appeal to owner precedence. -/
theorem preE7_completedSmallNumericalFamilyAction
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : PreE7CompletedSmallOwnerSourceData family w i) :
    preE7NoPairNoC3EarlierNumericalFamilyAction family w i :=
  preE7OrdinaryNumericalFamilyAction lit hgen (S.toOrdinarySource hgen hKP family)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
