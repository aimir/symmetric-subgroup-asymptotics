import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortCentralizerCardinality
import SymmetricSubgroupAsymptotics.CFSGHomConjugateOrbitCardinality

/-! The orbit of each of the six signed long root lines under the SAME
fixed positive matrix group has size charged to q^3 actual centralizers. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongRootOrbitCardinality
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckShortCentralizerCardinality
open CFSGTrialityGeckSectionHeightMembership CFSGTrialityD4InvariantRoots
open CFSGTrialityGeckFixedPositiveCardinality CFSGSerreOrdinaryTwists

local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) :=
  Classical.decEq _

def longRootOrbit (q : CFSG.PrimePower) (neg : Bool) (s : Fin 3) :=
  Set.range (fun u : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3) =>
    (RootLine (q.Extension 3) (signedLongRoot neg s)).map
      (MulAut.conj (fixedPositiveInclusion (q.Extension 3)
        (definingFieldAutomorphism q 3) u)).toMonoidHom)

theorem long_root_orbit_card_mul_centralizer_le (q : CFSG.PrimePower)
    (neg : Bool) (s : Fin 3) :
    Nat.card (longRootOrbit q neg s) *
      Nat.card (longCentralizer (q.Extension 3) (definingFieldAutomorphism q 3) neg s) ≤
        q.order ^ 12 := by
  have h := CFSGHomConjugateOrbitCardinality.image_card_mul_comap_centralizer_le
    (fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3))
    (RootLine (q.Extension 3) (signedLongRoot neg s))
  change Nat.card (longRootOrbit q neg s) *
    Nat.card (longCentralizer (q.Extension 3) (definingFieldAutomorphism q 3) neg s) ≤
      Nat.card (fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3)) at h
  exact h.trans_eq (fixedPositive_card q)

theorem long_root_orbit_card_mul_cube_le (q : CFSG.PrimePower)
    (neg : Bool) (s : Fin 3) :
    Nat.card (longRootOrbit q neg s) * q.order ^ 3 ≤ q.order ^ 12 :=
  (Nat.mul_le_mul_left _ (longCentralizer_card_lower q neg s)).trans
    (long_root_orbit_card_mul_centralizer_le q neg s)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongRootOrbitCardinality
