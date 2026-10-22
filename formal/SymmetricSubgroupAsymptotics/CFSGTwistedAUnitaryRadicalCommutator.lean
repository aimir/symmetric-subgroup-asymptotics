import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadical
import Mathlib.GroupTheory.Commutator.Basic

/-! The exact two-step commutator of the literal radical arrays. The
signed central parameter is a surjective Frobenius-difference expression
in every quadratic extension, including q=2. This gives a route to
central derived membership without a moving-torus assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [CommRing K] [Fintype J] [DecidableEq J]

theorem upperUnit_mul (w v w' v' : J → K) (b b' : K) :
    upperUnit w v b * upperUnit w' v' b' =
      upperUnit (w + w') (v + v') (b + b' + dotProduct w v') := by
  apply Units.ext
  exact upperArray_mul w v w' v' b b'

theorem upperUnit_inv (w v : J → K) (b : K) :
    (upperUnit w v b)⁻¹ = upperUnit (-w) (-v) (-b + dotProduct w v) := by
  apply Units.ext
  rfl

theorem upperUnit_commutator (w v w' v' : J → K) (b b' : K) :
    ⁅upperUnit w v b, upperUnit w' v' b'⁆ =
      upperUnit 0 0 (dotProduct w v' - dotProduct w' v) := by
  simp only [commutatorElement_def, upperUnit_inv, upperUnit_mul]
  have hw : w + w' + -w + -w' = 0 := by abel
  have hv : v + v' + -v + -v' = 0 := by abel
  rw [hw, hv]
  apply congrArg (upperUnit (0 : J → K) 0)
  simp only [add_dotProduct, dotProduct_neg, neg_dotProduct]
  ring

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParameters
open CFSGSerreOrdinaryTwists

theorem exists_signedCentral_commutator_parameter (q : CFSG.PrimePower)
    (eps c : q.Extension 2) (heps : eps = 1 ∨ eps = -1)
    (hc : definingFieldAutomorphism q 2 c + eps * c = 0) :
    ∃ t : q.Extension 2, eps * t - definingFieldAutomorphism q 2 t = c := by
  have hneg : -eps = 1 ∨ -eps = -1 := by
    rcases heps with rfl | rfl <;> simp
  have hsc : definingFieldAutomorphism q 2 (-c) = (-eps) * (-c) := by
    rw [map_neg]
    have hs : definingFieldAutomorphism q 2 c = -(eps * c) := eq_neg_of_add_eq_zero_left hc
    rw [hs]
    ring
  obtain ⟨t, ht⟩ := exists_signedTrace_eq q (-eps) (-c) hneg hsc
  refine ⟨t, ?_⟩
  calc
    eps * t - definingFieldAutomorphism q 2 t =
        -(definingFieldAutomorphism q 2 t + -eps * t) := by ring
    _ = c := by rw [ht, neg_neg]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParameters
