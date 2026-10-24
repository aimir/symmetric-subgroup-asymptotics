import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckDiagramPeriod
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckHighestDiagramFixed
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckHeightTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeEquiv
import SymmetricSubgroupAsymptotics.FiniteOrderFixedCentralDefect

/-! An actual middle radical word with diagram-fixed first coefficient
is itself fixed in characteristic different from three. Its actual
highest-root defect is pointwise fixed and has no three-torsion. This
proves genuine fixedness of each lift, rather than assuming descent of
quotient fixed points. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedLift

open CFSGTrialityD4NormTwo CFSGNormTwoRootPairing CFSGSerreDiagram
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckRootSubgroupTwist CFSGNormTwoCartanDiagramRoots
open CFSGNormTwoCartanDiagramWords CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateSelectedRootAdditive CFSGNormTwoCoordinateAllRootParameters
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeEquiv
open CFSGTrialityGeckMiddleFixedLayer CFSGGradedMatrixGroupFirstLayer
open CFSGGTwoD4GeckDiagramPeriod CFSGGTwoD4GeckHighestDiagramFixed
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem middle_twist_le (K : Type) [Field K] :
    (middleRadical K).map (unitTwist K (RingEquiv.refl K)).toMonoidHom ≤ middleRadical K := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨k,hk,hkmid,a,rfl⟩
  change unitTwist K (RingEquiv.refl K) (selectedRootElement A hd hs hp ho K k a) ∈ middleRadical K
  let theta := rootPermutation A trialityPermutation triality_preserves k
  have hm : unitTwist K (RingEquiv.refl K) (selectedRootElement A hd hs hp ho K k a) ∈
      rootSubgroup A hd hs hp ho K theta := by
    dsimp only [theta]
    rw [←root_subgroup_twist K (RingEquiv.refl K) k]
    exact ⟨_,selectedRootElement_mem A hd hs hp ho K k a,rfl⟩
  obtain ⟨b,hb⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K theta _).mp hm
  rw [←hb]
  apply middle_root_mem K theta
  · exact rootPermutation_positive A trialityPermutation triality_preserves k hk
  · have hi : trialityPermutation.symm (1 : Fin 4) = 1 := by
      apply trialityPermutation.injective
      rw [Equiv.apply_symm_apply]
      rfl
    change 1 ≤ k.val (trialityPermutation.symm 1)
    rw [hi]
    exact hkmid

theorem fixed_of_fixed_firstLayer (K : Type) [Field K] [Finite K]
    (hthree : (3 : K) ≠ 0) (u : middleRadical K)
    (hu : matrixTwist K (RingEquiv.refl K) (firstLayer middleWeight u.val) =
      firstLayer middleWeight u.val) : unitTwist K (RingEquiv.refl K) u.val = u.val := by
  let T := unitTwist K (RingEquiv.refl K)
  have htu : T u.val ∈ middleRadical K := middle_twist_le K ⟨u.val,u.property,rfl⟩
  let d : middleRadical K := ⟨T u.val*u.val⁻¹,
    (middleRadical K).mul_mem htu ((middleRadical K).inv_mem u.property)⟩
  have hcov : firstLayer middleWeight (T u.val) = firstLayer middleWeight u.val :=
    (matrixTwist_firstLayer K (RingEquiv.refl K) u.val).symm.trans hu
  have hz : firstLayer middleWeight d.val = 0 := by
    change firstLayer middleWeight (T u.val*u.val⁻¹) = 0
    rw [firstLayer_mul middleWeight _ _ (middle_le_strict K htu)
      (middle_le_strict K ((middleRadical K).inv_mem u.property)),
      firstLayer_inv middleWeight u.val (middle_le_strict K u.property),hcov,add_neg_cancel]
  have hk : d ∈ (middleFirstLayerHom K).ker := hz
  rw [firstLayer_kernel_eq_highest] at hk
  have hr : T u.val*u.val⁻¹ ∈ (selectedRootHom A hd hs hp ho K (longRoot 2)).range := by
    obtain ⟨a,ha⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K (longRoot 2) d.val).mp hk
    exact ⟨Multiplicative.ofAdd a,ha⟩
  exact FiniteOrderFixedCentralDefect.fixed_of_field_defect T 3 (unitTwist_pow_three K) hthree
    (selectedRootHom A hd hs hp ho K (longRoot 2))
    (selected_rootHom_injective A hd hs hp ho K (longRoot 2))
    (fun a => highest_selected_fixed K a.toAdd) u.val hr

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedLift
