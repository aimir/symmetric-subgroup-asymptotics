import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePerfect
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateQuarticSecondNegative
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckImageWeylWitness
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCentralKernel

/-! The action on the SAME original Serre image has central kernel in
all characteristics. Integral quartic formulas recover both divided-power
second coefficients from original E/F generators. No faithfulness premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateImageCentralKernel
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckImageWeylWitness
open CFSGNormTwoGeckHeightData
open CFSGNormTwoCoordinateQuarticSecondNegative CFSGSerreQuadraticCentralKernel
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

include hd hs hp ho
theorem exists_adjacent_to [Nontrivial (Fin r)] (i : Fin r) :
    ∃ j : Fin r, i ≠ j ∧ A i j = -1 := by
  obtain ⟨a, ha⟩ := exists_ne i
  by_contra hn
  push Not at hn
  have hall : ∀ a : Fin r, a = i := by
    intro a
    apply CFSGNormTwoCoordinateDominantSupport.coordinate_cartan_induction
      A hd hs hp ho (fun b => b = i) i a rfl
    intro b c hb hcb
    subst b
    by_contra hci
    have hcA := CFSGNormTwoCoordinateNormalSimpleRootGeneration.offdiagonal_nonzero_eq_neg_one
      A hd hs hp ho c i hci hcb
    have hiA : A i c = -1 := (congrFun (congrFun hs c) i).trans hcA
    exact hn c (Ne.symm hci) hiA
  exact ha (hall a)

theorem imageAction_kernel_le_center (K : Type) [Field K] [Nontrivial (Fin r)] :
    (imageAction A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K).ker ≤
      Subgroup.center (canonicalElementaryGroup D K) := by
  apply kernel_le_center_of_second D K
    (CFSGNormTwoGeckImageFourthCoefficient.baseChange_image_fourth_coefficient_zero
      A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K)
  intro g hg neg i
  obtain ⟨j, hij, hA⟩ := exists_adjacent_to A hd hs hp ho i
  have hA' : A j i = -1 := (congrFun (congrFun hs i) j).trans hA
  have hX (b : Bool) (k : Fin r) := kernel_commutes_root D K
    (CFSGNormTwoGeckImageFourthCoefficient.baseChange_image_fourth_coefficient_zero
      A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K) g hg b k
  cases neg with
  | false =>
    have hc := ((((hX false i).mul_right (hX false j)).sub_right
      ((hX false j).mul_right (hX false i))).mul_right (hX true j)).pow_right 2
    change Commute (g.val : Matrix _ _ K)
      ((⁅fieldRoot D K false i, fieldRoot D K false j⁆ * fieldRoot D K true j)^2) at hc
    rw [field_positive_quartic A hd hs hp ho K i j hij hA hA'] at hc
    simpa only [neg_neg] using hc.neg_right
  | true =>
    have hc := ((((hX true i).mul_right (hX true j)).sub_right
      ((hX true j).mul_right (hX true i))).mul_right (hX false j)).pow_right 2
    change Commute (g.val : Matrix _ _ K)
      ((⁅fieldRoot D K true i, fieldRoot D K true j⁆ * fieldRoot D K false j)^2) at hc
    rw [field_negative_quartic A hd hs hp ho K i j hij hA hA'] at hc
    simpa only [neg_neg] using hc.neg_right

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateImageCentralKernel
