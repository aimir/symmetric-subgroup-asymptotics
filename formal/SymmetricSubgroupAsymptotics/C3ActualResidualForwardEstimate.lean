import SymmetricSubgroupAsymptotics.C3ResidualForwardEstimate
import SymmetricSubgroupAsymptotics.C3ActualResidualClosure

/-! The exact existing residual kernel closes after excluding both owner
sectors. Its deleted degree and original complement stay unchanged. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open Filter
open scoped BigOperators

/-- Ambient-degree form of the complete final residual C3 family. -/
def c3ActualFinalResidualRatio (n : ℕ) : ℝ :=
  if 3 ≤ n then
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (FusionAcceptedOrbitPredicate ternaryRegularAction
        (C3ActualFinalResidualPredicate (n-3)))) : ℝ) / exactBenchmark n
  else 0

theorem c3ActualFinalResidualRatio_le_forwardRow
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (n : ℕ) (hn : 3 ≤ n) :
    c3ActualFinalResidualRatio n ≤
      ∑ b ∈ Finset.range n,
        c3FinalResidualForwardKernel n b * ordinarySubgroupRatio b := by
  have hadd : n - 3 + 3 = n := by omega
  have hlocal := c3ActualFinalResidual_physical_frontier
    hChief hWeight hgen hindex published8 h18 (n-3)
  have hrow := fusionForwardRow_weighted_sum
    (fun _ : Unit => 3) (fun _ => c3FinalResidualKernelFactor)
    (fun _ => by norm_num) ordinarySubgroupRatio n (fun _ => hn)
  unfold c3ActualFinalResidualRatio
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
noncomputable def c3ActualFinalResidual_exponentialForwardEstimate
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3ActualFinalResidualRatio := by
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
    exact (c3ActualFinalResidualRatio_le_forwardRow
      hChief hWeight hgen hindex published8 h18 n hn3).trans_eq (zero_add _).symm
  · intro n _
    positivity
  · intro n hn
    exact hN n ((le_max_right 3 N).trans hn)

end SymmetricSubgroupAsymptotics

end
