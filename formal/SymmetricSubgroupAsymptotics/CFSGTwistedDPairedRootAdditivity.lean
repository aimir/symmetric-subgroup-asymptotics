import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedRootImages
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOrthogonalRootCommutation

/-! The natural paired root line is additive. This theorem is only about
literal natural matrix units; original-source additivity is not assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPairedRootAdditivity
open CFSGSerreOrdinaryTwists CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationForkTorus CFSGTwistedDPairedFixedRoots
open CFSGTwistedDPairedRootImages CFSGOrthogonalDOrthogonalRootCommutation

theorem pairedNaturalRoot_zero (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) :
    pairedNaturalRoot s q neg 0 = 1 := by
  change rootElement (q.Extension 2) (s + 4) neg (pen (s + 2)) 0 *
    rootElement (q.Extension 2) (s + 4) neg (last (s + 2)) (0 ^ q.order) = 1
  have hq : q.order ≠ 0 := by
    have hpos : 0 < q.order := pow_pos q.prime_isPrime.pos q.exponent
    exact Nat.ne_of_gt hpos
  rw [(zero_pow hq : (0 : q.Extension 2)^q.order = 0),
    rootElement_zero, rootElement_zero, mul_one]

theorem pairedNaturalRoot_add (s : ℕ) (q : CFSG.PrimePower) (neg : Bool)
    (a b : q.Extension 2) :
    pairedNaturalRoot s q neg (a + b) =
      pairedNaturalRoot s q neg a * pairedNaturalRoot s q neg b := by
  have hpow : (a + b) ^ q.order = a ^ q.order + b ^ q.order := by
    simpa only [definingFieldAutomorphism_apply] using (definingFieldAutomorphism q 2).map_add a b
  have hc := rootElement_commute (q.Extension 2) (s + 4) (by omega)
    (pen (s + 2)) (last (s + 2)) (pen_ne_last (s + 2)) (fork_cartan_zero s)
    neg neg b (a ^ q.order)
  change rootElement (q.Extension 2) (s + 4) neg (pen (s + 2)) (a + b) *
    rootElement (q.Extension 2) (s + 4) neg (last (s + 2)) ((a + b) ^ q.order) =
    (rootElement (q.Extension 2) (s + 4) neg (pen (s + 2)) a *
      rootElement (q.Extension 2) (s + 4) neg (last (s + 2)) (a ^ q.order)) *
    (rootElement (q.Extension 2) (s + 4) neg (pen (s + 2)) b *
      rootElement (q.Extension 2) (s + 4) neg (last (s + 2)) (b ^ q.order))
  rw [hpow, rootElement_add, rootElement_add]
  exact hc.mul_mul_mul_comm _ _

theorem pairedNaturalRoot_inv (s : ℕ) (q : CFSG.PrimePower) (neg : Bool)
    (a : q.Extension 2) :
    (pairedNaturalRoot s q neg a)⁻¹ = pairedNaturalRoot s q neg (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pairedNaturalRoot_add, add_neg_cancel, pairedNaturalRoot_zero]

end SymmetricSubgroupAsymptotics.CFSGTwistedDPairedRootAdditivity
