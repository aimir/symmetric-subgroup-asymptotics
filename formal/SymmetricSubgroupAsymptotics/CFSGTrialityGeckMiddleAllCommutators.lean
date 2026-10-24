import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedCommutators
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedHighestParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootElementRange

/-! All actual middle radical commutators lie on the highest line, as a
consequence of the proved commutative quotient. In the actual fixed
radical, their parameters belong to the literal Frobenius-fixed field.
No lifting of fixed quotient points is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleAllCommutators

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleFixedCommutators CFSGTrialityGeckFixedPositiveRaw
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckFixedHighestParameters
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootElementRange
open CFSGTrialityFixedField CFSGSerreOrdinaryTwists
open scoped commutatorElement

local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem middle_commutator_mem_highest (K : Type) [Field K] (u v : middleRadical K) :
    ⁅u.val, v.val⁆ ∈ highestLine K := by
  letI : IsMulCommutative (MiddleQuotient K) := quotient_isMulCommutative K
  have he : (QuotientGroup.mk' (highestInMiddle K)) ⁅u, v⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' _ _
  have hm := (QuotientGroup.eq_one_iff ⁅u, v⁆).mp he
  exact hm

theorem fixed_middle_commutator_parameter (q : CFSG.PrimePower) (u v : fixedMiddle q) :
    ∃ t : fixedField q,
      selectedRootElement A hd hs hp ho (q.Extension 3) (longRoot 2) t.val = ⁅u.val, v.val⁆ := by
  let c : Raw (q.Extension 3) := ⁅u.val, v.val⁆
  have hm : c ∈ highestLine (q.Extension 3) :=
    middle_commutator_mem_highest (q.Extension 3) ⟨u.val, u.property.1⟩ ⟨v.val, v.property.1⟩
  obtain ⟨t, ht⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho (q.Extension 3)
    (longRoot 2) c).mp hm
  have hu := ((mem_fixedPositiveRaw_iff q u.val).mp u.property.2).2
  have hv := ((mem_fixedPositiveRaw_iff q v.val).mp v.property.2).2
  have hcomm : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) c = c := by
    dsimp only [c]
    rw [map_commutatorElement, hu, hv]
  have htf : definingFieldAutomorphism q 3 t = t :=
    fixed_highest_parameter q t
      ((congrArg (unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)) ht).trans
        (hcomm.trans ht.symm))
  exact ⟨⟨t, htf⟩, ht⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleAllCommutators
