import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleOuterKernel
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleInitialCoordinate
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRaisedKernel
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDerivedFirstLayer

/-! The actual fixed positive group's derived subgroup is exactly the
kernel of its original simple leading coordinates. The difficult lower
inclusion uses fixed-word norm-curve lifts and fixed long-A2 central
commutators, including q=2 and characteristic three. No surjectivity of
fixed points onto a quotient, nor ambient fixed-group recognition, is
assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveDerivedKernel
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckFixedPositiveRaw
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleOuterKernel
open CFSGTrialityGeckMiddleLayerCoordinates CFSGTrialityGeckMiddleInitialCoordinate
open CFSGTrialityGeckMiddleRaisedKernel CFSGTrialityGeckMiddleFixedCommutators
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoCoordinateRootHeightLeading CFSGNormTwoCoordinateHeight
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckLatticeDegree
open CFSGTrialityGeckMatrixTwist CFSGSerreOrdinaryTwists
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixLieFirstLayer
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem fixedPositiveRaw_le_positive (q : CFSG.PrimePower) :
    fixedPositiveRaw q ≤ Positive (q.Extension 3) := by
  intro u hu
  exact ((mem_fixedPositiveRaw_iff q u).mp hu).1

def fixedLeadingHom (q : CFSG.PrimePower) :
    fixedPositiveRaw q →* Multiplicative (Fin 4 → q.Extension 3) :=
  (leadingHom A hd hs hp ho (q.Extension 3)).comp
    (Subgroup.inclusion (fixedPositiveRaw_le_positive q))

private theorem weight_eq :
    weight A hs hp (CFSGNormTwoRootPairing.coordinateBase A hd hs hp ho) coordinateHeight =
      heightWeight A hd hs hp ho := by
  funext j
  rcases j with j | j
  · simp [weight,heightWeight,latticeWeight,CFSGIntegerHeightSign.height]
  · rfl

theorem leading_zero_mem_positiveDerived (q : CFSG.PrimePower) (u : fixedPositiveRaw q)
    (hzero : leadingCoordinates A hd hs hp ho (q.Extension 3) u.val = 0) :
    u.val ∈ positiveDerived q := by
  have hpositive := fixedPositiveRaw_le_positive q u.property
  have hR := mem_middle_of_leading_zero (q.Extension 3) ⟨u.val,hpositive⟩ hzero
  have hfixed := ((mem_fixedPositiveRaw_iff q u.val).mp u.property).2
  obtain ⟨c,hc,hcoordinates⟩ := exists_fixed_firstLayer_coordinates q ⟨u.val,hR⟩ hfixed
  have hheight : firstLayer (heightWeight A hd hs hp ho) u.val = 0 := by
    have he := positive_firstLayer_eq_coordinates A hd hs hp ho (q.Extension 3) u.val hpositive
    rw [weight_eq] at he
    rw [he,hzero]
    simp only [Pi.zero_apply,zero_smul,Finset.sum_const_zero]
  have h0 := initial_coordinate_zero (q.Extension 3) u.val c hcoordinates.symm hheight
  exact fixed_middle_mem_derived_of_zero_initial q ⟨u.val,hR⟩ hfixed c hc hcoordinates h0

theorem fixed_leading_kernel_eq_derived (q : CFSG.PrimePower) :
    (fixedLeadingHom q).ker = commutator (fixedPositiveRaw q) := by
  apply le_antisymm _ (Abelianization.commutator_subset_ker (fixedLeadingHom q))
  intro u hu
  have hzero : leadingCoordinates A hd hs hp ho (q.Extension 3) u.val = 0 :=
    congrArg Multiplicative.toAdd (show fixedLeadingHom q u = 1 from hu)
  obtain ⟨d,hdval⟩ := leading_zero_mem_positiveDerived q u hzero
  have he : d.val = u := Subtype.ext hdval
  exact he ▸ d.property

theorem mem_positiveDerived_iff_leading_zero (q : CFSG.PrimePower) (u : fixedPositiveRaw q) :
    u.val ∈ positiveDerived q ↔ leadingCoordinates A hd hs hp ho (q.Extension 3) u.val = 0 := by
  constructor
  · rintro ⟨d,hdval⟩
    have he : d.val = u := Subtype.ext hdval
    have hu : u ∈ commutator (fixedPositiveRaw q) := he ▸ d.property
    rw [← fixed_leading_kernel_eq_derived] at hu
    exact congrArg Multiplicative.toAdd (show fixedLeadingHom q u = 1 from hu)
  · exact leading_zero_mem_positiveDerived q u

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveDerivedKernel
