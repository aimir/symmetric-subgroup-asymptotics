import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedLiftSpan
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleHighestDerived
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeEquiv

/-! A fixed middle-radical word whose initial tensor coordinate vanishes
is an ACTUAL commutator-group element. The seven raised coordinates are
lifted by fixed commutators; the remaining literal highest-root kernel
is supplied by the fixed long A2 commutators. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRaisedKernel
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleRadicalQuotient CFSGTrialityGeckMiddleCubeEquiv
open CFSGTrialityGeckMiddleTensorCovariance CFSGTrialityGeckMiddleFixedCommutators
open CFSGTrialityGeckMiddleFixedLiftSpan CFSGTrialityGeckMiddleHighestDerived
open CFSGTrialityGeckFixedPositiveRaw CFSGTrialityGeckMatrixTwist
open CFSGTrialityMiddleFixedTensorSpan CFSGCubicTensorEnvelopeDimension
open CFSGCubicTensorAugmentationDimension CFSGSerreOrdinaryTwists
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixSubgroups
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem fullEnvelope_tail (q : CFSG.PrimePower) (c : Fin 8 → q.Extension 3)
    (hc : c ∈ fullEnvelope q) : (fun i : Fin 7 => c i.succ) ∈ raisedEnvelope q := by
  obtain ⟨p,hpvec⟩ := hc
  refine ⟨(p.2.1,p.2.2.1,p.2.2.2),?_⟩
  rw [← hpvec]
  funext i
  fin_cases i <;> rfl

theorem tensorCoordinates_zero_initial (K : Type) [Field K] (c : Fin 8 → K) (hc : c 0 = 0) :
    tensorCoordinates K c = raisedTensorCoordinates K (fun i : Fin 7 => c i.succ) := by
  change (∑ i : Fin 8, c i • actualTensor K i) =
    ∑ i : Fin 7, c i.succ • actualTensor K i.succ
  rw [Fin.sum_univ_succ,hc,zero_smul,zero_add]

theorem positiveDerived_le_fixedPositive (q : CFSG.PrimePower) :
    positiveDerived q ≤ fixedPositiveRaw q := by
  rintro x ⟨d,rfl⟩
  exact d.val.property

theorem fixed_middle_mem_derived_of_zero_initial (q : CFSG.PrimePower)
    (u : middleRadical (q.Extension 3))
    (hfixed : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) u.val = u.val)
    (c : Fin 8 → q.Extension 3) (hc : c ∈ fullEnvelope q)
    (hcoeff : tensorCoordinates (q.Extension 3) c = firstLayer middleWeight u.val)
    (hzero : c 0 = 0) : u.val ∈ positiveDerived q := by
  obtain ⟨v,hv⟩ := derived_raisedEnvelope_lifts q (fun i : Fin 7 => c i.succ)
    (fullEnvelope_tail q c hc)
  have hlayers : firstLayer middleWeight u.val = firstLayer middleWeight v.val :=
    hcoeff.symm.trans ((tensorCoordinates_zero_initial _ c hzero).trans hv.symm)
  let vR : middleRadical (q.Extension 3) := ⟨v.val,v.property.1⟩
  let w : middleRadical (q.Extension 3) := u*vR⁻¹
  have hwlayer : firstLayer middleWeight w.val = 0 := by
    change firstLayer middleWeight (u.val*v.val⁻¹) = 0
    rw [firstLayer_mul middleWeight _ _ (middle_le_strict _ u.property)
      ((strictUnits middleWeight).inv_mem (middle_le_strict _ v.property.1)),
      firstLayer_inv middleWeight _ (middle_le_strict _ v.property.1), ← hlayers,add_neg_cancel]
  have hwkernel : w ∈ (middleFirstLayerHom (q.Extension 3)).ker := by
    change firstLayer middleWeight w.val = 0
    exact hwlayer
  have hwZ : w.val ∈ highestLine (q.Extension 3) := by
    have h : w ∈ highestInMiddle (q.Extension 3) := by
      rwa [← firstLayer_kernel_eq_highest]
    exact h
  have hvfixed := ((mem_fixedPositiveRaw_iff q _).mp
    (positiveDerived_le_fixedPositive q v.property.2)).2
  have hwfixed : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) w.val = w.val := by
    change unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) (u.val*v.val⁻¹) = u.val*v.val⁻¹
    rw [map_mul,map_inv,hfixed,hvfixed]
  have hwderived := highest_fixed_mem_derived q w.val hwZ hwfixed
  have hm := (positiveDerived q).mul_mem hwderived v.property.2
  change (u.val*v.val⁻¹)*v.val ∈ positiveDerived q at hm
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRaisedKernel
