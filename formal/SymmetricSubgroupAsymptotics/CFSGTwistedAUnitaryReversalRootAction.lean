import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryReversalWeyl
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalReversal
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryEndpointPair

/-! The SAME signed reversal exchanges positive and negative natural
root units with the exact minus sign and reversed node. The endpoint
paired fixed roots are consequently carried to their actual opposite
paired fixed roots. No group-generation or derived premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists

theorem signedReversal_rootMatrix (K : Type) [Field K] (r : ℕ)
    (neg : Bool) (i : Fin r) :
    (signedReversalUnit K r : Mat K r) * rootMatrix K r neg i *
      (↑((signedReversalUnit K r)⁻¹) : Mat K r) = -rootMatrix K r (!neg) i.rev := by
  cases neg
  · have h := matrixDiagram_negative K r i
    change (signedReversalUnit K r : Mat K r) * (-positive K r i) *
      (↑((signedReversalUnit K r)⁻¹) : Mat K r) = negative K r i.rev at h
    simpa only [mul_neg, neg_mul, neg_neg] using congrArg Neg.neg h
  · have h := matrixDiagram_positive K r i
    change (signedReversalUnit K r : Mat K r) * (-negative K r i) *
      (↑((signedReversalUnit K r)⁻¹) : Mat K r) = positive K r i.rev at h
    simpa only [mul_neg, neg_mul, neg_neg] using congrArg Neg.neg h

theorem signedReversal_rootUnit (K : Type) [Field K] (r : ℕ)
    (neg : Bool) (i : Fin r) (a : K) :
    signedReversalUnit K r * naturalRootUnit K r neg i a * (signedReversalUnit K r)⁻¹ =
      naturalRootUnit K r (!neg) i.rev (-a) := by
  apply Units.ext
  change (signedReversalUnit K r : Mat K r) * (1 + a • rootMatrix K r neg i) *
    (↑((signedReversalUnit K r)⁻¹) : Mat K r) = 1 + (-a) • rootMatrix K r (!neg) i.rev
  simp only [mul_add, add_mul, mul_one, Units.mul_inv, mul_smul_comm, smul_mul_assoc]
  rw [signedReversal_rootMatrix, smul_neg, neg_smul]

theorem reversal_conjugate_endpointPair (q : CFSG.PrimePower) (s : ℕ)
    (neg : Bool) (a : q.Extension 2) :
    reversalFixed q (s + 3) * endpointNaturalFixedPair q s neg a *
      (reversalFixed q (s + 3))⁻¹ =
        endpointNaturalFixedPair q s (!neg) (-(definingFieldAutomorphism q 2 a)) := by
  apply Subtype.ext
  apply Subtype.ext
  change signedReversalUnit (q.Extension 2) (s + 3) *
      (naturalRootUnit (q.Extension 2) (s + 3) neg (endpointNode s) a *
        naturalRootUnit (q.Extension 2) (s + 3) neg (endpointNode s).rev
          (definingFieldAutomorphism q 2 a)) * (signedReversalUnit (q.Extension 2) (s + 3))⁻¹ = _
  have hc := naturalRootUnit_commute_of_zero (s + 3) (!neg) (endpointNode s)
    (endpointNode s).rev (-(definingFieldAutomorphism q 2 a)) (-a)
    (endpoint_rootMatrix_mul_zero (q.Extension 2) s (!neg)).1
    (endpoint_rootMatrix_mul_zero (q.Extension 2) s (!neg)).2
  calc
    _ = (signedReversalUnit (q.Extension 2) (s + 3) *
        naturalRootUnit (q.Extension 2) (s + 3) neg (endpointNode s) a *
          (signedReversalUnit (q.Extension 2) (s + 3))⁻¹) *
        (signedReversalUnit (q.Extension 2) (s + 3) *
        naturalRootUnit (q.Extension 2) (s + 3) neg (endpointNode s).rev
          (definingFieldAutomorphism q 2 a) * (signedReversalUnit (q.Extension 2) (s + 3))⁻¹) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    _ = _ := by
      rw [signedReversal_rootUnit, signedReversal_rootUnit, Fin.rev_rev, hc.eq.symm]
      have ha : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 a) = a :=
        extension_two_pow_twice q a
      change naturalRootUnit (q.Extension 2) (s + 3) (!neg) (endpointNode s)
          (-(definingFieldAutomorphism q 2 a)) *
        naturalRootUnit (q.Extension 2) (s + 3) (!neg) (endpointNode s).rev (-a) =
        naturalRootUnit (q.Extension 2) (s + 3) (!neg) (endpointNode s)
          (-(definingFieldAutomorphism q 2 a)) *
        naturalRootUnit (q.Extension 2) (s + 3) (!neg) (endpointNode s).rev
          (definingFieldAutomorphism q 2 (-(definingFieldAutomorphism q 2 a)))
      rw [map_neg, ha]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
