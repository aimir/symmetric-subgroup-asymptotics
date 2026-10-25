import SymmetricSubgroupAsymptotics.CFSGUnitarySignedHermitianNormalization
import SymmetricSubgroupAsymptotics.CFSGQuadraticHermitianScaledBasis
import SymmetricSubgroupAsymptotics.FiniteHermitianScaledSpecialOrderBound
import SymmetricSubgroupAsymptotics.CFSGUnitarySpecialIsometryEquiv
import SymmetricSubgroupAsymptotics.CFSGUnitaryOriginalOrderUpper

/-! A sharp universal order envelope for the ORIGINAL unitary models.
The signed matrix is normalized by t^r, actual Gram--Schmidt gives its
basis, and the full determinant image supplies q+1. The existing original
natural fixed covers are retained; no unitary order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGHermitianSimilitudeGroup

theorem naturalFixed_card_mul_normOne_le_frame (q : CFSG.PrimePower) (r : ℕ) :
    (q.order+1)*Nat.card (naturalFixed r q) ≤ 3*q.order^((r+1)^2) := by
  obtain ⟨c,hc,hrec⟩ := CFSGUnitarySignedHermitianNormalization.exists_scalar_reciprocal q r
  obtain ⟨b,hb⟩ := CFSGQuadraticHermitianScaledBasis.exists_basis q
    (signedReversalUnit (q.Extension 2) r) c hc hrec
  have hh := FiniteHermitianScaledSpecialOrderBound.special_card_mul_normOne_le q
    (signedReversalUnit (q.Extension 2) r) c hc b hb
    (⟨0,by simp⟩ : Fin (Fintype.card (Fin (r+1))))
  have he : Nat.card (specialIsometries (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r))=Nat.card (naturalFixed r q) :=
    Nat.card_congr (naturalFixedSpecialIsometryEquiv q r).symm.toEquiv
  simpa only [he,Fintype.card_fin] using hh

theorem twistedA_admissible_order_mul_normOne_le_frame (r : ℕ) (hr : 2 ≤ r)
    (q : CFSG.PrimePower) (hsmall : r=2 → q.order≠2) :
    (q.order+1)*Nat.card (CFSG.Models.TwistedA r q) ≤ 3*q.order^((r+1)^2) := by
  by_cases htwo : r=2
  · subst r
    have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    have hq : 3 ≤ q.order := by have := hsmall rfl; omega
    exact (Nat.mul_le_mul_left (q.order+1)
      (Nat.card_le_card_of_surjective (rankTwoProjectiveCover q hq)
        (rankTwoProjectiveCover_surjective q hq))).trans
          (naturalFixed_card_mul_normOne_le_frame q 2)
  · obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
    exact (Nat.mul_le_mul_left (q.order+1)
      (Nat.card_le_card_of_surjective (unitaryProjectiveCover q s)
        (unitaryProjectiveCover_surjective q s))).trans
          (naturalFixed_card_mul_normOne_le_frame q (s+3))

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
