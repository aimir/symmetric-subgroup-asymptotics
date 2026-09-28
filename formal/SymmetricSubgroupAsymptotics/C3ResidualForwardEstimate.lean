import SymmetricSubgroupAsymptotics.C3ResidualClosure
import SymmetricSubgroupAsymptotics.FusionWidthContinuation
import SymmetricSubgroupAsymptotics.ForwardEstimateAlgebra

/-!
# A complete forward estimate for the residual C3 row

The closed c=1 residual family is placed at its literal complement degree.
The sum of the direct and low kernels has uniform exponential decay, giving
the complete forward-estimate object used by final frontier assembly.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

def c3FinalResidualKernelFactor (b : ℕ) : ℝ :=
  c3DirectAxisKernel b + c3TrivialLowKernel b

theorem c3FinalResidualKernelFactor_nonneg (b : ℕ) :
    0 ≤ c3FinalResidualKernelFactor b :=
  add_nonneg (c3DirectAxisKernel_nonneg b) (c3TrivialLowKernel_nonneg b)

theorem c3FinalResidualKernelFactor_eventually :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ b : ℕ in atTop,
      c3FinalResidualKernelFactor b ≤ C * (2 : ℝ) ^ (-κ * (b : ℝ)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := c3DirectAxisKernel_eventually
  obtain ⟨C₂, hC₂, h₂⟩ := c3TrivialLowKernel_eventually
  refine ⟨C₁ + C₂, 1 / 200, add_pos hC₁ hC₂, by norm_num, ?_⟩
  filter_upwards [h₁, h₂] with b hb₁ hb₂
  have hp : (2 : ℝ) ^ (-(1 / 8 : ℝ) * (b : ℝ)) ≤
      (2 : ℝ) ^ (-(1 / 200 : ℝ) * (b : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) b]
  calc
    c3FinalResidualKernelFactor b ≤
        C₁ * (2 : ℝ) ^ (-(1 / 8 : ℝ) * (b : ℝ)) +
          C₂ * (2 : ℝ) ^ (-(1 / 200 : ℝ) * (b : ℝ)) :=
      add_le_add hb₁ hb₂
    _ ≤ C₁ * (2 : ℝ) ^ (-(1 / 200 : ℝ) * (b : ℝ)) +
          C₂ * (2 : ℝ) ^ (-(1 / 200 : ℝ) * (b : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hp hC₁.le) le_rfl
    _ = (C₁ + C₂) * (2 : ℝ) ^ (-(1 / 200 : ℝ) * (b : ℝ)) := by ring

/-- One width-three row, supported at the literal complete complement. -/
def c3FinalResidualForwardKernel (n b : ℕ) : ℝ :=
  fusionForwardRow (fun _ : Unit => 3)
    (fun _ => c3FinalResidualKernelFactor) n b

theorem c3FinalResidualForwardKernel_nonneg (n b : ℕ) :
    0 ≤ c3FinalResidualForwardKernel n b :=
  fusionForwardRow_nonneg (fun _ : Unit => 3)
    (fun _ => c3FinalResidualKernelFactor)
    (fun _ => c3FinalResidualKernelFactor_nonneg) n b

theorem c3FinalResidualForwardKernel_decay :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      (∑ b ∈ Finset.range n, c3FinalResidualForwardKernel n b) ≤
        C * (2 : ℝ) ^ (-κ * (n : ℝ)) :=
  fusionForwardRow_decay (fun _ : Unit => 3)
    (fun _ => c3FinalResidualKernelFactor) (fun _ => by norm_num)
    (fun _ => c3FinalResidualKernelFactor_eventually)

/-- Ambient-degree form of the complete final residual C3 family. -/
def c3FinalResidualRatio (n : ℕ) : ℝ :=
  if 3 ≤ n then
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction
        (C3FinalResidualPredicate (n-3)))) : ℝ) / exactBenchmark n
  else 0

theorem c3FinalResidualRatio_le_forwardRow
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (n : ℕ) (hn : 3 ≤ n) :
    c3FinalResidualRatio n ≤
      ∑ b ∈ Finset.range n,
        c3FinalResidualForwardKernel n b * ordinarySubgroupRatio b := by
  have hadd : n - 3 + 3 = n := by omega
  have hlocal := c3FinalResidual_physical_frontier
    hChief hWeight hPrimitive h18 (n-3)
  have hrow := fusionForwardRow_weighted_sum
    (fun _ : Unit => 3) (fun _ => c3FinalResidualKernelFactor)
    (fun _ => by norm_num) ordinarySubgroupRatio n (fun _ => hn)
  unfold c3FinalResidualRatio
  rw [if_pos hn]
  rw [hadd] at hlocal
  have hrow' : (∑ b ∈ Finset.range n,
      c3FinalResidualForwardKernel n b * ordinarySubgroupRatio b) =
        c3FinalResidualKernelFactor (n-3) *
          ordinarySubgroupRatio (n-3) := by
    simpa only [c3FinalResidualForwardKernel, Fintype.sum_unique] using hrow
  exact hlocal.trans_eq hrow'.symm

/-- The c=1 residual sector is now a complete exponentially contractive
forward estimate, with no surviving high scalar term. -/
noncomputable def c3FinalResidual_exponentialForwardEstimate
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3FinalResidualRatio := by
  let W := c3FinalResidualForwardKernel_decay
  let C : ℝ := Classical.choose W
  have hCκ := Classical.choose_spec W
  let κ : ℝ := Classical.choose hCκ
  have hdecaySpec := Classical.choose_spec hCκ
  have hC : 0 < C := hdecaySpec.1
  have hκ : 0 < κ := hdecaySpec.2.1
  have hdecay := hdecaySpec.2.2
  let V := eventually_atTop.mp hdecay
  let N : ℕ := Classical.choose V
  have hN := Classical.choose_spec V
  refine
    { scalar := fun _ => 0
      kernel := c3FinalResidualForwardKernel
      threshold := max 3 N
      rate := κ
      scalarConst := 1
      rowConst := C
      rate_pos := hκ
      scalarConst_pos := by norm_num
      rowConst_nonneg := hC.le
      kernel_nonneg := ?_
      recurrence := ?_
      scalar_decay := ?_
      row_decay := ?_ }
  · intro n _ b _
    exact c3FinalResidualForwardKernel_nonneg n b
  · intro n hn
    have hn3 : 3 ≤ n := (le_max_left 3 N).trans hn
    exact (c3FinalResidualRatio_le_forwardRow
      hChief hWeight hPrimitive h18 n hn3).trans_eq (zero_add _).symm
  · intro n _
    positivity
  · intro n hn
    exact hN n ((le_max_right 3 N).trans hn)

end SymmetricSubgroupAsymptotics

end
