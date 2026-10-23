import SymmetricSubgroupAsymptotics.CFSGTrialityD4MiddleCube
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDiagramCovariance
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightCommutator

/-! The actual D4 root words of positive middle degree commute modulo
one literal highest root subgroup. The highest subgroup commutes with
all these generators. No fixed-field, quotient-coordinate, or derived
subgroup identification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalCommutators
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4MiddleCube
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinatePositivePairCollecting
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (Roots A) := Classical.decEq _

private theorem not_opposite (k l : Roots A)
    (hk : ∀ i, 0 ≤ k.val i) (hl : ∀ i, 0 ≤ l.val i) : k.val ≠ -l.val := by
  intro he
  have hz : k.val = 0 := by
    funext j
    have hj := congrFun he j
    have hkj := hk j
    have hlj := hl j
    change k.val j = -(l.val j) at hj
    change k.val j = 0
    omega
  have hn := k.property
  rw [hz] at hn
  norm_num at hn

private theorem commutator_eq_one {G : Type*} [Group G] (x y : G)
    (hc : Commute x y) : x*y*x⁻¹*y⁻¹=1 := by
  rw [hc.eq]
  group

theorem middle_positive_commutator_mem_highest (K : Type) [Field K]
    (k l : Roots A) (hk : ∀ i, 0 ≤ k.val i) (hl : ∀ i, 0 ≤ l.val i)
    (hkmid : 1 ≤ k.val 1) (hlmid : 1 ≤ l.val 1) (a b : K) :
    selectedRootElement A hd hs hp ho K k a * selectedRootElement A hd hs hp ho K l b *
      (selectedRootElement A hd hs hp ho K k a)⁻¹ *
      (selectedRootElement A hd hs hp ho K l b)⁻¹ ∈
        rootSubgroup A hd hs hp ho K (longRoot 2) := by
  by_cases hkl : k = l
  · subst l
    rw [commutator_eq_one _ _ (selectedRootElement_commute A hd hs hp ho K k a b)]
    exact Subgroup.one_mem _
  rcases root_pairing_interior A hs hp k l hkl (not_opposite k l hk hl) with hneg | hother
  · obtain ⟨ε, _, hcollect⟩ := positive_pair_commutator_sign A hd hs hp ho k l hk hl hneg
    rw [hcollect K a b]
    have hsum : sumRoot A hs k l hneg = longRoot 2 := by
      apply positive_middle_ge_two_eq_highest
      · exact fun i => add_nonneg (hk i) (hl i)
      · change 2 ≤ k.val 1 + l.val 1
        omega
    rw [hsum]
    exact selectedRootElement_mem A hd hs hp ho K (longRoot 2) _
  · have hc := CFSGNormTwoCoordinatePositivePairCommute.positive_pair_commute
      A hd hs hp ho K k l hk hl hother a b
    rw [commutator_eq_one _ _ hc]
    exact Subgroup.one_mem _

theorem highest_commutes_middle_positive (K : Type) [Field K]
    (k : Roots A) (hk : ∀ i, 0 ≤ k.val i) (hkmid : 1 ≤ k.val 1) (a b : K) :
    Commute (selectedRootElement A hd hs hp ho K (longRoot 2) a)
      (selectedRootElement A hd hs hp ho K k b) := by
  by_cases hsame : longRoot 2 = k
  · subst k
    exact selectedRootElement_commute A hd hs hp ho K (longRoot 2) a b
  rcases root_pairing_interior A hs hp (longRoot 2) k hsame
      (not_opposite (longRoot 2) k (long_positive 2) hk) with hneg | hother
  · have hsum := positive_middle_ge_two_eq_highest (sumRoot A hs (longRoot 2) k hneg)
      (fun i => add_nonneg (long_positive 2 i) (hk i)) (by
        change 2 ≤ 2 + k.val 1
        omega)
    have he := congrArg (fun r : Roots A => r.val 1) hsum
    change 2 + k.val 1 = 2 at he
    omega
  · exact CFSGNormTwoCoordinatePositivePairCommute.positive_pair_commute
      A hd hs hp ho K (longRoot 2) k (long_positive 2) hk hother a b

theorem cube_commutator_mem_highest (K : Type) [Field K] (u v : Cube) (a b : K) :
    selectedRootElement A hd hs hp ho K (cubeRoot u) a *
      selectedRootElement A hd hs hp ho K (cubeRoot v) b *
      (selectedRootElement A hd hs hp ho K (cubeRoot u) a)⁻¹ *
      (selectedRootElement A hd hs hp ho K (cubeRoot v) b)⁻¹ ∈
        rootSubgroup A hd hs hp ho K (longRoot 2) :=
  middle_positive_commutator_mem_highest K (cubeRoot u) (cubeRoot v)
    (cubeRoot_positive u) (cubeRoot_positive v) (by rw [cubeRoot_middle])
    (by rw [cubeRoot_middle]) a b

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalCommutators
