import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRootAxisPairing

/-! The full signed reciprocal equation for the literal natural
Hermitian pairing, with no division by two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters

theorem unitaryNaturalPair_signed_reciprocal (q : CFSG.PrimePower) (r : ℕ)
    (v w : Fin (r + 1) → q.Extension 2) :
    unitaryNaturalPair q r v w = (-1 : q.Extension 2)^r *
      definingFieldAutomorphism q 2 (unitaryNaturalPair q r w v) := by
  have he2 : ((-1 : q.Extension 2)^r) * ((-1 : q.Extension 2)^r) = 1 := by
    rw [← mul_pow]
    simp
  have hm : (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r).map
      (definingFieldAutomorphism q 2) = signedReversalUnit (q.Extension 2) r :=
    map_signedReversalUnit_val (definingFieldAutomorphism q 2).toRingHom r
  have hform : (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r).map
      (definingFieldAutomorphism q 2) = ((-1 : q.Extension 2)^r) •
        (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r).transpose := by
    rw [hm, signedReversalUnit_transpose, smul_smul, he2, one_smul]
  have hh := hermitianPair_sigma (definingFieldAutomorphism q 2)
    (fun a => extension_two_pow_twice q a) ((-1 : q.Extension 2)^r)
    (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) hform w v
  change definingFieldAutomorphism q 2 (unitaryNaturalPair q r w v) =
    ((-1 : q.Extension 2)^r) * unitaryNaturalPair q r v w at hh
  rw [hh, ← mul_assoc, he2, one_mul]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
