import SymmetricSubgroupAsymptotics.CFSGHermitianIsometryOrderBound
import SymmetricSubgroupAsymptotics.CFSGUnitaryOriginalOrderUpper
import Mathlib.Algebra.Ring.Parity

/-! Basis-prefix isometry counting sharpens the matrix-space upper
bound on the same original unitary model. The actual natural covers
and literal defining-fixed equation are retained in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem naturalFixed_card_le_isometry_power (q : CFSG.PrimePower) (r : ℕ) :
    Nat.card (naturalFixed r q) ≤ q.order ^ ((r+1)*(r+2)) := by
  let rho : naturalFixed r q →* (Mat (q.Extension 2) r)ˣ :=
    (NaturalElementary (q.Extension 2) r).subtype.comp (naturalFixed r q).subtype
  have hinj : Function.Injective rho :=
    (NaturalElementary (q.Extension 2) r).subtype_injective.comp
      (naturalFixed r q).subtype_injective
  have h := CFSGHermitianIsometryOrderBound.card_le_pairing_power rho hinj
    (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2)
    ((signedReversalUnit (q.Extension 2) r)⁻¹) (fun g =>
      fixed_unit_isometric (q.Extension 2) r
        (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom g.val.val g.property)
  rw [extension_two_card, ← pow_mul] at h
  have he : 2*((r+1)*((r+1)+1)/2) = (r+1)*(r+2) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one (r+1))
  rwa [he] at h

theorem twistedA_admissible_order_le_isometry_power (r : ℕ) (hr : 2 ≤ r)
    (q : CFSG.PrimePower) (hsmall : r=2 → q.order≠2) :
    Nat.card (CFSG.Models.TwistedA r q) ≤ q.order ^ ((r+1)*(r+2)) := by
  by_cases htwo : r=2
  · subst r
    have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    have hq : 3 ≤ q.order := by have := hsmall rfl; omega
    exact (Nat.card_le_card_of_surjective (rankTwoProjectiveCover q hq)
      (rankTwoProjectiveCover_surjective q hq)).trans
        (naturalFixed_card_le_isometry_power q 2)
  · obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
    exact (Nat.card_le_card_of_surjective (unitaryProjectiveCover q s)
      (unitaryProjectiveCover_surjective q s)).trans
        (naturalFixed_card_le_isometry_power q (s+3))

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
