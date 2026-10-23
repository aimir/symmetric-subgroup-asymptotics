import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedCommutators
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOuterParameterChart

/-! The actual middle radical is the kernel of the three OUTER simple
leading coordinates on the original positive group. Strict middle
triangularity kills those entries; the checked genuine complement
factorization and its independent parameters prove the converse. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleOuterKernel
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMiddleRadicalQuotient CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleRadicalCardinality CFSGTrialityGeckMiddleFixedCommutators
open CFSGTrialityGeckOuterParameterChart CFSGTrialityGeckShortComplementFactor
open CFSGTrialityGeckShortComplementUnique CFSGTrialityGeckPositiveTwist
open CFSGNormTwoCoordinateLeadingFactor CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckColumns CFSGTrialityFixedWeylWords
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

def middlePositiveHom (K : Type) [Field K] : middleRadical K →* Positive K :=
  Subgroup.inclusion (middle_le_positive K)

theorem outerLeading_middle (K : Type) [Field K] (u : middleRadical K) :
    outerLeadingHom K (middlePositiveHom K u) = 1 := by
  funext j
  change (u.val : Mat K) (Sum.inl (Index (outerNode j)))
    (Sum.inr (negativeIndex A hs hp (Index (outerNode j)))) = 0
  have hw : middleWeight (Sum.inl (Index (outerNode j))) ≤
      middleWeight (Sum.inr (negativeIndex A hs hp (Index (outerNode j)))) := by
    change (0 : ℤ) ≤ (negativeIndex A hs hp (Index (outerNode j))).val 1
    rw [negative_val]
    change (0 : ℤ) ≤ -(Index (outerNode j) : CFSGNormTwoRootPairing.Roots A).val 1
    rw [outer_simple_central_zero]
    exact le_rfl
  rw [middle_le_strict K u.property _ _ hw, Matrix.one_apply,
    if_neg Sum.inl_ne_inr]

theorem mem_middle_of_outerLeading_eq_one (K : Type) [Field K]
    (u : Positive K) (hu : outerLeadingHom K u = 1) : u.val ∈ middleRadical K := by
  obtain ⟨c,hc,a,he⟩ := positive_short_factor K u.val u.property
  have hcR : c ∈ middleRadical K := by rwa [middleRadical_eq_shortComplement]
  let v : Positive K := ⟨c,middle_le_positive K hcR⟩
  have hprod : u = v * outerPositiveHom K a := Subtype.ext he
  have hcoordinates := congrArg (outerLeadingHom K) hprod
  rw [map_mul, show outerLeadingHom K v = 1 from outerLeading_middle K ⟨c,hcR⟩,
    outer_leading_left_inverse, one_mul, hu] at hcoordinates
  rw [he, ← hcoordinates, map_one, mul_one]
  exact hcR

theorem mem_middle_of_leading_zero (K : Type) [Field K] (u : Positive K)
    (hu : leadingCoordinates A (CartanMatrix.D_diag 4) hs hp
      (CartanMatrix.D_off_diag_nonpos 4) K u.val = 0) : u.val ∈ middleRadical K := by
  apply mem_middle_of_outerLeading_eq_one K u
  funext j
  change leadingCoordinates A (CartanMatrix.D_diag 4) hs hp
    (CartanMatrix.D_off_diag_nonpos 4) K u.val (outerNode j) = 0
  exact congrFun hu (outerNode j)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleOuterKernel
