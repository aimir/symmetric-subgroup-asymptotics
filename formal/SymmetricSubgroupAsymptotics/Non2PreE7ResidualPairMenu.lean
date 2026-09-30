import SymmetricSubgroupAsymptotics.Non2PreE7PairFiniteMenu

/-!
# The four residual pre-E7 pair widths

The nonbinary action exhaustion leaves twelve large pair counts.  The first
eight are exactly the selected `E7` menu and hence are absent from the
pre-`E7` action index.  This file instantiates the universal finite-menu
consumer on the four remaining half-widths `384, 768, 1536, 3072`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

inductive PreE7ResidualPairCountLabel
  | c384 | c768 | c1536 | c3072
  deriving DecidableEq, Fintype

def PreE7ResidualPairCountLabel.pairCount :
    PreE7ResidualPairCountLabel → ℕ
  | .c384 => 384
  | .c768 => 768
  | .c1536 => 1536
  | .c3072 => 3072

theorem PreE7ResidualPairCountLabel.pairCount_ge_24
    (d : PreE7ResidualPairCountLabel) :
    24 ≤ d.pairCount := by
  cases d <;> decide

theorem PreE7ResidualPairCountLabel.pairCount_even
    (d : PreE7ResidualPairCountLabel) :
    Even d.pairCount := by
  cases d <;> norm_num [pairCount]

theorem PreE7ResidualPairCountLabel.sourceDegree_le_6144
    (d : PreE7ResidualPairCountLabel) :
    2 * d.pairCount ≤ 6144 := by
  cases d <;> decide

/-- The exact physical union of the four residual pair-width menus. -/
abbrev PreE7ResidualPairPhysical :=
  PreE7PairMenuPhysical PreE7ResidualPairCountLabel.pairCount

/-- Its ambient-degree normalized count. -/
abbrev preE7ResidualPairPhysicalRatio :=
  preE7PairMenuPhysicalRatio PreE7ResidualPairCountLabel.pairCount

/-- Complete forward estimate for all pair-action cells which survive the
selected `E7` removal in the action exhaustion. -/
noncomputable def preE7ResidualPairPhysical_exponentialForwardEstimate
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7ResidualPairPhysicalRatio :=
  preE7PairMenuPhysical_exponentialForwardEstimate
    PreE7ResidualPairCountLabel.pairCount hTracey hExceptional
    PreE7ResidualPairCountLabel.pairCount_ge_24
    PreE7ResidualPairCountLabel.pairCount_even 6144
    PreE7ResidualPairCountLabel.sourceDegree_le_6144

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
