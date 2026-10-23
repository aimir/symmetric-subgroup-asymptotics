import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortLowestCommutant
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortCentralizerCardinality

/-! A genuinely central fixed-positive element has vanishing simple
brackets at its lowest height. The three outer directions are separated
by the full cubic parameter, including q=2 and characteristic three. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCentralLowest
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckShortLowestCommutant CFSGTrialityGeckShortCentralizerCardinality
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckSectionQuotientCoordinates
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckFixedRootSections
open CFSGTrialityGeckHeightQuotientTwist CFSGTrialityGeckPositiveTwist
open CFSGNormTwoCoordinateRootHeightSupport CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinateCenterHeightLeading CFSGSerreQuadraticMatrix
open CFSGSerreOrdinaryTwists
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

private theorem central_map_commute {G H : Type*} [Group G] [Group H]
    (f : G →* H) (z : G) (hz : z ∈ Subgroup.center G) (x : G) : Commute (f z) (f x) := by
  change f z*f x=f x*f z
  rw [←map_mul,←map_mul]
  exact congrArg f ((Subgroup.mem_center_iff.mp hz) x).symm

theorem central_commutes_short (q : CFSG.PrimePower)
    (u : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3))
    (hz : u ∈ Subgroup.center _) (t : q.Extension 3) :
    fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3) u *
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t =
    shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t *
      fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3) u := by
  have hh := (central_map_commute
    (fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3)) u hz
    (shortFixedElement (q.Extension 3) (definingFieldAutomorphism q 3)
      (CFSGTrialityTripleFixedRoots.extension_three_pow_thrice q) 0 t)).eq
  rw [shortFixedElement_val] at hh
  simpa only [shortSection,shortTransport,Matrix.cons_val_zero,inv_one,one_mul,mul_one] using hh

theorem central_commutes_middle (q : CFSG.PrimePower)
    (u : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3))
    (hz : u ∈ Subgroup.center _) :
    fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3) u *
        canonicalRoot rawData (q.Extension 3) false 1 1 =
      canonicalRoot rawData (q.Extension 3) false 1 1 *
        fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3) u := by
  let z : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3) :=
    ⟨longPositiveSection (q.Extension 3) 0 (Multiplicative.ofAdd 1),
      longPositiveSection_fixed (q.Extension 3) (definingFieldAutomorphism q 3) 0
        (Multiplicative.ofAdd 1) (map_one _)⟩
  have hval : fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3) z =
      canonicalRoot rawData (q.Extension 3) false 1 1 := by
    change (longPositiveSection (q.Extension 3) 0 (Multiplicative.ofAdd 1)).val = _
    rw [longPositiveSection_val]
    change (1 : (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ) *
      canonicalRoot rawData (q.Extension 3) false 1 1 * 1⁻¹ =
        canonicalRoot rawData (q.Extension 3) false 1 1
    simp only [inv_one,one_mul,mul_one]
  have hh := (central_map_commute
    (fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3)) u hz z).eq
  rw [hval] at hh
  exact hh

theorem central_lowest_brackets_zero (q : CFSG.PrimePower) (h : ℤ) (hh : 0<h)
    (u : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3))
    (hu : u.val ∈ TailInPositive (q.Extension 3) h) (hz : u ∈ Subgroup.center _)
    (i : Fin 4) :
    ⁅fieldRoot rawData (q.Extension 3) false i,
      lowestPart (q.Extension 3) h u.val.val⁆=0 := by
  have hcut := heightTail_belowCut A hd hs hp ho (q.Extension 3) h hh u.val.val hu
  have hout := short_commutation_lowest_brackets q h u.val.val hcut
    (central_commutes_short q u hz)
  have hmid : ⁅fieldRoot rawData (q.Extension 3) false 1,
      lowestPart (q.Extension 3) h u.val.val⁆=0 :=
    lowest_bracket_zero_of_commutes A hd hs hp ho (q.Extension 3) h hh u.val hu 1
      (central_commutes_middle q u hz)
  fin_cases i
  · exact hout.1
  · exact hmid
  · exact hout.2.1
  · exact hout.2.2

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCentralLowest
