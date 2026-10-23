import SymmetricSubgroupAsymptotics.CFSGTrialityD4HighestMiddleReflection
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalQuotient
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFirstLayer
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixTransportStrict
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixOpposite

/-! The literal highest-root Weyl word reverses the actual middle grading.
Hence an actual middle-radical word commuting with it is the identity.
This uses integer support, not coefficient-field eigenvalues or a group
order/recognition theorem. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckHighestWeylMiddleGrade
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4HighestMiddleReflection CFSGTrialityGeckSectionRootLabels
open CFSGTrialityGeckFixedRootSections CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleFirstLayer CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWordLatticeSupport CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport
open CFSGGradedMatrixSubgroups CFSGGradedMatrixTransportStrict
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ell" => latticeWeight A hs hp Base
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

def highestReflectionWord : List (Fin 4) :=
  (longWord 2 ++ [1]) ++ inverseWord (longWord 2)

theorem highestReflectionWord_linear :
    wordLinear A hs hp Base Index highestReflectionWord = highestReflectionLinear := by
  rw [highestReflectionWord,wordLinear_append,wordLinear_append,wordLinear_inverseWord]
  change (highestTransportLinear * ((reflectionEquiv A (Index 1)).toIntLinearEquiv * 1)) *
    highestTransportLinear⁻¹ = highestReflectionLinear
  rw [mul_one]
  rfl

def highestWeyl (K : Type) [Field K] : Raw K :=
  wordUnit A hs hp Base Index K highestReflectionWord

theorem highestWeyl_eq (K : Type) [Field K] :
    highestWeyl K = longTransport K 2 * canonicalWeyl rawData K 1 * (longTransport K 2)⁻¹ := by
  have hT : wordUnit A hs hp Base Index K (longWord 2) = longTransport K 2 :=
    (word_eq_canonicalWord A hs hp Base Index K (longWord 2)).trans (longTransport_word K 2).symm
  rw [highestWeyl,highestReflectionWord,wordUnit_append,wordUnit_append,wordUnit_inverseWord,hT]
  simp only [wordUnit,mul_one]
  rfl

theorem highestWeyl_root_word (K : Type) [Field K] :
    highestWeyl K = longSection K 2 false 1 * longSection K 2 true (-1) *
      longSection K 2 false 1 := by
  rw [highestWeyl_eq]
  simp only [longSection,canonicalWeyl]
  group

theorem highestWeyl_lattice_support (K : Type) [Field K] :
    Supported ell highestReflectionLinear (highestWeyl K).val := by
  have h := word_lattice_support A hs hp Base Index K highestReflectionWord
  rw [highestReflectionWord_linear] at h
  exact h

theorem highestWeyl_inverse_lattice_support (K : Type) [Field K] :
    Supported ell highestReflectionLinear.symm (↑((highestWeyl K)⁻¹) : Mat K) := by
  have h := word_lattice_support A hs hp Base Index K (inverseWord highestReflectionWord)
  rw [wordUnit_inverseWord,wordLinear_inverseWord,highestReflectionWord_linear] at h
  exact h

theorem highestReflection_inverse_middle (x : Fin 4 → ℤ) :
    (highestReflectionLinear.symm x) 1 = -(x 1) := by
  have h := highestReflection_middle (highestReflectionLinear.symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  omega

theorem highestWeyl_conjugate_middle_opposite (K : Type) [Field K] (u : Raw K)
    (hu : u ∈ middleRadical K) :
    highestWeyl K * u * (highestWeyl K)⁻¹ ∈ strictUnits (fun i => -middleWeight i) := by
  have h := conjugate_mem_strict ell (fun x : Fin 4 → ℤ => x 1) highestReflectionLinear.toEquiv
    (highestWeyl K) (highestWeyl_lattice_support K) (highestWeyl_inverse_lattice_support K)
    u (middle_le_strict K hu)
  have hweight : (fun i : GeckIndex => (highestReflectionLinear.symm (ell i)) 1) =
      fun i => -middleWeight i := funext (fun i => highestReflection_inverse_middle (ell i))
  change highestWeyl K * u * (highestWeyl K)⁻¹ ∈
    strictUnits (fun i : GeckIndex => (highestReflectionLinear.symm (ell i)) 1) at h
  rw [hweight] at h
  exact h

theorem middle_commuting_highestWeyl_eq_one (K : Type) [Field K] (u : Raw K)
    (hu : u ∈ middleRadical K) (hc : Commute u (highestWeyl K)) : u = 1 := by
  have hop := highestWeyl_conjugate_middle_opposite K u hu
  have he : highestWeyl K * u * (highestWeyl K)⁻¹ = u := by
    rw [← hc.eq,mul_assoc,mul_inv_cancel,mul_one]
  rw [he] at hop
  have hm : u ∈ strictUnits middleWeight ⊓ strictUnits (fun i => -middleWeight i) :=
    ⟨middle_le_strict K hu,hop⟩
  rwa [strict_inf_opposite,Subgroup.mem_bot] at hm

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckHighestWeylMiddleGrade
