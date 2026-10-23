import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalQuotient
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalRootTail
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupFirstLayer
import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticFirstCoefficient

/-! Literal middle-degree first coefficients of the actual radical.
They form an additive homomorphism, kill the highest root subgroup,
and therefore descend to its genuine central quotient. No injectivity
of this descended map is assumed or claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFirstLayer
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleRadicalQuotient
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoCoordinateRootHeightLeading
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootCoefficientCoordinates
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootElementRange
open CFSGGradedMatrixSupport CFSGGradedQuadraticUnit
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixSingleDegreeSpan
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (Roots A) := Classical.decEq _

abbrev Mat (K : Type) := Matrix GeckIndex GeckIndex K

def middleFunctional : (Fin 4 → ℤ) →ₗ[ℤ] ℤ := LinearMap.proj 1

def middleWeight (i : GeckIndex) : ℤ :=
  middleFunctional (latticeWeight A hs hp Base i)

theorem middle_le_strict (K : Type) [Field K] :
    middleRadical K ≤ CFSGGradedMatrixSubgroups.strictUnits middleWeight := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨k, hk, hkmid, a, rfl⟩
  exact CFSGNormTwoCoordinateFunctionalRootTail.selected_root_strict
    A hd hs hp ho K middleFunctional k (by change 0 < k.val 1; omega) a

theorem root_firstLayer (K : Type) [Field K] (k : Roots A) (hmid : k.val 1 = 1) (a : K) :
    firstLayer middleWeight (selectedRootElement A hd hs hp ho K k a) =
      a • selectedFieldCoefficient A hd hs hp ho K k := by
  let E : Mat K := selectedFieldCoefficient A hd hs hp ho K k
  let D : Mat K := selectedSecondCoefficient A hd hs hp ho K k
  let u : Raw K := selectedRootElement A hd hs hp ho K k a
  have hexp : (u.val : Mat K) = 1 + a • E + a^2 • D :=
    selectedRootElement_expansion A hd hs hp ho K k a
  have hE := support_apply_height (latticeWeight A hs hp Base) k.val
    middleFunctional.toAddMonoidHom _ (selectedFieldCoefficient_support A hd hs hp ho K k)
  have hD := support_apply_height (latticeWeight A hs hp Base) (k.val + k.val)
    middleFunctional.toAddMonoidHom _ (selectedSecondCoefficient_support A hd hs hp ho K k)
  change Supported middleWeight (fun w => w + k.val 1) E at hE
  change Supported middleWeight (fun w => w + (k.val 1 + k.val 1)) D at hD
  rw [hmid] at hE hD
  change degreePart (I := GeckIndex) middleWeight 1 ((u.val : Mat K) - 1) = a • E
  rw [hexp]
  have hdev : (1 + a • E + a^2 • D : Mat K) - 1 = a • E + a^2 • D := by abel
  rw [hdev, map_add, map_smul, map_smul, degreePart_eq _ _ _ hE,
    degreePart_zero_of_other _ 1 (1+1) _ hD (by norm_num), smul_zero, add_zero]

theorem highest_firstLayer (K : Type) [Field K] (a : K) :
    firstLayer middleWeight (selectedRootElement A hd hs hp ho K (longRoot 2) a) = 0 := by
  let E : Mat K := selectedFieldCoefficient A hd hs hp ho K (longRoot 2)
  let D : Mat K := selectedSecondCoefficient A hd hs hp ho K (longRoot 2)
  let u : Raw K := selectedRootElement A hd hs hp ho K (longRoot 2) a
  have hexp : (u.val : Mat K) = 1 + a • E + a^2 • D :=
    selectedRootElement_expansion A hd hs hp ho K (longRoot 2) a
  have hE := support_apply_height (latticeWeight A hs hp Base) (longRoot 2).val
    middleFunctional.toAddMonoidHom _
    (selectedFieldCoefficient_support A hd hs hp ho K (longRoot 2))
  have hD := support_apply_height (latticeWeight A hs hp Base) ((longRoot 2).val + (longRoot 2).val)
    middleFunctional.toAddMonoidHom _
    (selectedSecondCoefficient_support A hd hs hp ho K (longRoot 2))
  change Supported middleWeight (fun w => w + 2) E at hE
  change Supported middleWeight (fun w => w + (2+2)) D at hD
  change degreePart (I := GeckIndex) middleWeight 1 ((u.val : Mat K) - 1) = 0
  rw [hexp, map_sub, map_add, map_add, map_smul, map_smul,
    degreePart_zero_of_other _ 1 0 1 (by
      simpa only [add_zero] using (supported_one (R := K) middleWeight)) (by norm_num),
    degreePart_zero_of_other _ 1 2 _ hE (by norm_num),
    degreePart_zero_of_other _ 1 (2+2) _ hD (by norm_num)]
  simp only [smul_zero, add_zero, sub_zero]

def middleFirstLayerHom (K : Type) [Field K] :
    middleRadical K →* Multiplicative (Mat K) where
  toFun u := Multiplicative.ofAdd (firstLayer middleWeight u.val)
  map_one' := congrArg Multiplicative.ofAdd (firstLayer_one middleWeight)
  map_mul' u v := congrArg Multiplicative.ofAdd
    (firstLayer_mul middleWeight u.val v.val (middle_le_strict K u.property)
      (middle_le_strict K v.property))

theorem highest_le_firstLayer_kernel (K : Type) [Field K] :
    highestInMiddle K ≤ (middleFirstLayerHom K).ker := by
  intro x hx
  obtain ⟨a, ha⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K (longRoot 2) x.val).mp hx
  change firstLayer middleWeight x.val = 0
  rw [← ha, highest_firstLayer]

def quotientFirstLayerHom (K : Type) [Field K] :
    MiddleQuotient K →* Multiplicative (Mat K) :=
  QuotientGroup.lift (highestInMiddle K) (middleFirstLayerHom K)
    (highest_le_firstLayer_kernel K)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFirstLayer
