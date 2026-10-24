import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedLongLine
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongA2Commutator

/-! The selected highest-root parameter is transformed by the actual
defining field map. An actual fixed element on that line therefore has
its parameter in the literal fixed field. This is a raw root-line fact,
not a quotient fixed-point lifting assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedHighestParameters

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckFixedRootSections
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckFixedLongLine
open CFSGTrialityGeckLongA2Commutator CFSGSerreOrdinaryTwists
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateAllRootParameters
open CFSGNormTwoCoordinateSelectedRootAdditive

local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem highest_selected_twist (q : CFSG.PrimePower) (t : q.Extension 3) :
    unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (selectedRootElement A hd hs hp ho (q.Extension 3) (longRoot 2) t) =
    selectedRootElement A hd hs hp ho (q.Extension 3) (longRoot 2)
      (definingFieldAutomorphism q 3 t) := by
  obtain ⟨ε, hε, he⟩ := longSection_selected_sign 2
  have hsquare : (ε : q.Extension 3) * (ε : q.Extension 3) = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  have hparam (s : q.Extension 3) : longSection (q.Extension 3) 2 false ((ε : q.Extension 3) * s) =
      selectedRootElement A hd hs hp ho (q.Extension 3) (longRoot 2) s := by
    rw [he]
    apply congrArg (selectedRootElement A hd hs hp ho (q.Extension 3) (longRoot 2))
    rw [← mul_assoc, hsquare, one_mul]
  calc
    _ = unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
        (longSection (q.Extension 3) 2 false ((ε : q.Extension 3) * t)) :=
      congrArg (unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)) (hparam t).symm
    _ = longSection (q.Extension 3) 2 false
        (definingFieldAutomorphism q 3 ((ε : q.Extension 3) * t)) := highest_long_twist q _
    _ = longSection (q.Extension 3) 2 false
        ((ε : q.Extension 3) * definingFieldAutomorphism q 3 t) := by rw [map_mul, map_intCast]
    _ = _ := hparam _

theorem fixed_highest_parameter (q : CFSG.PrimePower) (t : q.Extension 3)
    (ht : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (selectedRootElement A hd hs hp ho (q.Extension 3) (longRoot 2) t) =
        selectedRootElement A hd hs hp ho (q.Extension 3) (longRoot 2) t) :
    definingFieldAutomorphism q 3 t = t := by
  have he := (highest_selected_twist q t).symm.trans ht
  have hh : Multiplicative.ofAdd (definingFieldAutomorphism q 3 t) = Multiplicative.ofAdd t :=
    selected_rootHom_injective A hd hs hp ho (q.Extension 3) (longRoot 2) he
  exact congrArg Multiplicative.toAdd hh

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedHighestParameters
