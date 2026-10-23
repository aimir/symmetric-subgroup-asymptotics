import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCentralLowest
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLowestBracketPeeling
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongRootFamilyCover

/-! A central element of the genuine triality-fixed positive group has
no coordinates below the highest D4 root. Four literal height steps use
the cubic-parameter lowest-bracket tests, uniformly in characteristic. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCentralPeeling
open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4PositiveRootIndex
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckFixedCentralLowest
open CFSGTrialityGeckShortLowestCommutant CFSGTrialityGeckHeightQuotientTwist
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckFixedPositiveGeneration
open CFSGTrialityGeckLongRootFamilyCover CFSGNormTwoCoordinateLowestBracketPeeling
open CFSGIntegerHeightSign CFSGSerreOrdinaryTwists
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem highest_long_height : height (longRoot 2).val=5 := by
  change (∑i,(longRoot 2).val i)=5
  exact long_height 2

theorem central_mem_next_tail (q : CFSG.PrimePower) (h : ℤ) (hh : 0<h) (hh5 : h<5)
    (u : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3))
    (hu : u.val∈TailInPositive (q.Extension 3) h) (hz : u∈Subgroup.center _) :
    u.val∈TailInPositive (q.Extension 3) (h+1) := by
  apply mem_next_tail_of_lowest_brackets_zero A hd hs hp ho (q.Extension 3)
    (longRoot 2) (long_positive 2) highest_long_dominant h hh
  · rw [highest_long_height]
    omega
  · exact hu
  · intro i
    exact central_lowest_brackets_zero q h hh u hu hz i

theorem central_mem_tail_five (q : CFSG.PrimePower)
    (u : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3))
    (hz : u∈Subgroup.center _) : u.val∈TailInPositive (q.Extension 3) 5 := by
  have h1 : u.val∈TailInPositive (q.Extension 3) 1 := by
    rw [first_tail_eq_top]
    exact Subgroup.mem_top _
  have h2 := central_mem_next_tail q 1 (by decide) (by decide) u h1 hz
  have h3 := central_mem_next_tail q 2 (by decide) (by decide) u h2 hz
  have h4 := central_mem_next_tail q 3 (by decide) (by decide) u h3 hz
  exact central_mem_next_tail q 4 (by decide) (by decide) u h4 hz

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCentralPeeling
