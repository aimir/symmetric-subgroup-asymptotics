import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborAutomorphism
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTriples

/-! The original D4 root-plane stabilizer acts on its intrinsic twin
quotient as an actual Hamming-relation permutation on the three original
flag-coordinate types. No action on endpoints is supplied externally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDIndexTrialityD4HammingTwins CFSGOrthogonalDIndexTrialityD4HammingEdges
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
variable (f : MulAut (elementaryProjective K 4))
  (hfix : singularActionHom K p 0 f (originalRootPlane K) = originalRootPlane K)

theorem originalTwinPermutation_closed (x y : NeighborTwinQuotient K) :
    TwoCoordinates (quotientFlags K (originalTwinQuotientPermutation K p f hfix x))
      (quotientFlags K (originalTwinQuotientPermutation K p f hfix y)) ↔
        TwoCoordinates (quotientFlags K x) (quotientFlags K y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro S T
  change TwoCoordinates (neighborFlagMap K (originalNeighborPermutation K p f hfix S))
    (neighborFlagMap K (originalNeighborPermutation K p f hfix T)) ↔
      TwoCoordinates (neighborFlagMap K S) (neighborFlagMap K T)
  rw [← neighbor_closed_adj_iff, ← neighbor_closed_adj_iff]
  exact originalNeighborPermutation_preserves_closed K p f hfix S T

def originalFlagPermutation : Equiv.Perm
    (RootPoints K × (RulingParameters K × RulingParameters K)) :=
  (neighborTwinQuotientEquiv K).symm.trans
    ((originalTwinQuotientPermutation K p f hfix).trans (neighborTwinQuotientEquiv K))

theorem originalFlagPermutation_closed
    (x y : RootPoints K × (RulingParameters K × RulingParameters K)) :
    TwoCoordinates (originalFlagPermutation K p f hfix x)
      (originalFlagPermutation K p f hfix y) ↔ TwoCoordinates x y := by
  have hh := originalTwinPermutation_closed K p f hfix
    ((neighborTwinQuotientEquiv K).symm x) ((neighborTwinQuotientEquiv K).symm y)
  change TwoCoordinates (originalFlagPermutation K p f hfix x)
    (originalFlagPermutation K p f hfix y) ↔
      TwoCoordinates ((neighborTwinQuotientEquiv K) ((neighborTwinQuotientEquiv K).symm x))
        ((neighborTwinQuotientEquiv K) ((neighborTwinQuotientEquiv K).symm y)) at hh
  simpa only [Equiv.apply_symm_apply] using hh

abbrev OriginalResidueFamily := TripleFamily (RootPoints K) (RulingParameters K) (RulingParameters K)
abbrev OriginalResidueCoordinates := (i : Fin 3) → OriginalResidueFamily K i

def originalResidueCoordinatePermutation : Equiv.Perm (OriginalResidueCoordinates K) :=
  (tripleEquiv (RootPoints K) (RulingParameters K) (RulingParameters K)).symm.trans
    ((originalFlagPermutation K p f hfix).trans
      (tripleEquiv (RootPoints K) (RulingParameters K) (RulingParameters K)))

theorem originalResidueCoordinatePermutation_closed (x y : OriginalResidueCoordinates K) :
    ClosedAdjacent (originalResidueCoordinatePermutation K p f hfix x)
      (originalResidueCoordinatePermutation K p f hfix y) ↔ ClosedAdjacent x y := by
  let e := tripleEquiv (RootPoints K) (RulingParameters K) (RulingParameters K)
  have hleft := triple_closedAdjacent_iff (RootPoints K) (RulingParameters K) (RulingParameters K)
    (originalFlagPermutation K p f hfix (e.symm x))
    (originalFlagPermutation K p f hfix (e.symm y))
  have hright := triple_closedAdjacent_iff (RootPoints K) (RulingParameters K) (RulingParameters K)
    (e.symm x) (e.symm y)
  have hh := hleft.trans ((originalFlagPermutation_closed K p f hfix (e.symm x) (e.symm y)).trans hright.symm)
  change ClosedAdjacent (originalResidueCoordinatePermutation K p f hfix x)
    (originalResidueCoordinatePermutation K p f hfix y) ↔
      ClosedAdjacent (e (e.symm x)) (e (e.symm y)) at hh
  simpa only [Equiv.apply_symm_apply] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
