import SymmetricSubgroupAsymptotics.Non2UnipotentPrefixPhysicalEstimate
import SymmetricSubgroupAsymptotics.ForwardEstimateAlgebra

/-!
# Complete forward estimate for the physical E7 owner

The exact original-weight row for the hot/cold E7 union is already strictly
forward and exponentially small.  This file packages it in the common
ambient-degree interface used by the final ordinary-frontier assembly.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Ambient-degree normalized count of the literal E7 hot/cold owner union. -/
def e7UPOwnedPhysicalRatio
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) : ℝ :=
  (Nat.card (E7UPOwnedPhysical hTracey hExceptional n) : ℝ) /
    exactBenchmark n

/-- The complete hot/cold E7 owner is an exponentially contractive forward
sector.  There is no high scalar term. -/
noncomputable def e7UPOwnedPhysical_exponentialForwardEstimate
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      (e7UPOwnedPhysicalRatio hTracey hExceptional) := by
  let W := e7UPPhysicalDirectRow_decay hTracey hExceptional
  let A : ℝ := Classical.choose W
  have hAκ := Classical.choose_spec W
  let κ : ℝ := Classical.choose hAκ
  have hdecaySpec := Classical.choose_spec hAκ
  have hA : 0 < A := hdecaySpec.1
  have hκ : 0 < κ := hdecaySpec.2.1
  have hdecay := hdecaySpec.2.2
  let V := eventually_atTop.mp hdecay
  let N : ℕ := Classical.choose V
  have hN := Classical.choose_spec V
  refine
    { scalar := fun _ => 0
      kernel := e7UPPhysicalDirectRow hTracey hExceptional
      threshold := max 512 N
      rate := κ
      scalarConst := 1
      rowConst := A
      rate_pos := hκ
      scalarConst_pos := by norm_num
      rowConst_nonneg := hA.le
      kernel_nonneg := ?_
      recurrence := ?_
      scalar_decay := ?_
      row_decay := ?_ }
  · intro n _ m _
    exact e7UPPhysicalDirectRow_nonneg hTracey hExceptional n m
  · intro n hn
    have hn512 : 512 ≤ n := (le_max_left 512 N).trans hn
    exact (e7UPOwnedPhysical_direct_recurrence
      hTracey hExceptional n hn512).trans_eq (zero_add _).symm
  · intro n _
    positivity
  · intro n hn
    exact hN n ((le_max_right 512 N).trans hn)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
