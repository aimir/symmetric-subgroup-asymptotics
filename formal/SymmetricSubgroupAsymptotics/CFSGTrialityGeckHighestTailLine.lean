import SymmetricSubgroupAsymptotics.CFSGTrialityGeckWordRootIndex
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionHeightMembership

/-! The fifth actual D4 height tail is contained in the literal highest
long root line. This uses the proved twelve-positive-root indexing,
not a named-group order or centre identification. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckHighestTailLine
open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4PositiveRootIndex
open CFSGTrialityGeckWordRootIndex CFSGTrialityGeckSectionRootLabels
open CFSGTrialityGeckSectionHeightMembership CFSGTrialityGeckHeightTwist
open CFSGNormTwoCoordinateRootHeightFiltration CFSGNormTwoCoordinateRootElementRange
open CFSGIntegerHeightSign CFSGTrialityGeckDiagramCovariance
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem positive_root_eq_highest_of_height_ge_five (k : Positive)
    (hk : 5≤height k.val.val) : k.val=longRoot 2 := by
  obtain ⟨a,rfl⟩ := wordPositiveRootEquiv.surjective k
  rcases a with s | ⟨s,j⟩
  · change 5≤height (longRoot s).val at hk
    change (longRoot s)=longRoot 2
    change 5≤(∑i,(longRoot s).val i) at hk
    rw [long_height] at hk
    fin_cases s <;> simp_all
  · change 5≤height (shortLabel s j).val at hk
    rw [short_label_height] at hk
    fin_cases s <;> norm_num at hk

theorem tail_five_le_highest_rootLine (K : Type) [Field K] :
    HeightTail K 5≤RootLine K (longRoot 2) := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨k,hk,a,rfl⟩
  have he := positive_root_eq_highest_of_height_ge_five k hk
  rw [he]
  exact (mem_rootSubgroup_iff_selected A hd hs hp ho K (longRoot 2) _).mpr ⟨a,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckHighestTailLine
