import SymmetricSubgroupAsymptotics.CFSGTwistedDResidualNeighbourData
import SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneAdjacencyActions

/-! An explicit injection of the residual singular-point chart into
common neighbours of the actual normalized R11 pair. No exact singular
point count or projective scalar-fibre estimate is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizedCommonNeighbours
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDHighestPairOperator
open CFSGTwistedDSingularPlaneOrbit CFSGTwistedDPlaneFamilyAction
open CFSGTwistedDResidualNeighbourData CFSGTwistedDResidualCorrection
open CFSGTwistedDDoubleTailEmbedding CFSGTwistedDSingularPointCharts
open CFSGTwistedDPlaneAdjacencyActions CFSGTwistedA2FixedField
open CFSGPolarCommonPointPlanes CFSGOrthogonalDIndexQuadraticCorrection

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

abbrev CommonNeighbours (s : ℕ) (q : CFSG.PrimePower) (P Q : SingularPlanes s q) :=
  {R : SingularPlanes s q // PlaneAdjacent s q P R ∧ PlaneAdjacent s q Q R}

def standardPlane (s : ℕ) (q : CFSG.PrimePower) : SingularPlanes s q :=
  ⟨standardRootPlane s q, standardRootPlane_finrank s q, standardRootPlane_singular s q⟩

def companionPlane (s : ℕ) (q : CFSG.PrimePower) (w : fixedSpace (s + 2) q)
    (hws : fixedQuadraticForm (s + 2) q w = 0)
    (hwu : (fixedQuadraticForm (s + 2) q).polarBilin w (firstVector s q) = 0)
    (hw : (fixedQuadraticForm (s + 2) q).polarBilin w (secondVector s q) ≠ 0) :
    SingularPlanes s q := by
  refine ⟨rightPlane s q w, rightPlane_finrank s q w hw, ?_⟩
  apply singular_span_pair
  · exact standardRootPlane_singular s q _ (Submodule.subset_span (Or.inl rfl))
  · exact hws
  · exact (QuadraticMap.polar_comm (fixedQuadraticForm (s + 2) q : _ → fixedField q) _ _).trans hwu

theorem residualPlane_finrank (s : ℕ) (q : CFSG.PrimePower)
    (w : fixedSpace (s + 2) q) (p : Parameters s q) :
    Module.finrank (fixedField q) (residualPlane s q w p) = 2 := by
  have hu : firstVector s q ≠ 0 :=
    CFSGTwistedDSingularDimensionBound.firstAxis_nonzero (s + 2) q
  apply pairPlane_finrank (firstVector s q) (residualMap s q w (chart s q p)) hu
  intro a he
  apply chart_nonzero s q p
  have hh := congrArg (doubleRestriction s q) he
  simpa only [residualMap_leftInverse, map_smul, doubleRestriction_first, smul_zero] using hh

theorem residualPlane_singular (s : ℕ) (q : CFSG.PrimePower)
    (w : fixedSpace (s + 2) q) (p : Parameters s q) :
    ∀ z ∈ residualPlane s q w p, fixedQuadraticForm (s + 2) q z = 0 := by
  apply singular_span_pair
  · exact standardRootPlane_singular s q _ (Submodule.subset_span (Or.inl rfl))
  · exact (residualMap_quadratic s q w _).trans (chart_singular s q p)
  · exact residualMap_perp_first s q w _

def chartNeighbour (s : ℕ) (q : CFSG.PrimePower) (w : fixedSpace (s + 2) q)
    (hws : fixedQuadraticForm (s + 2) q w = 0)
    (hwu : (fixedQuadraticForm (s + 2) q).polarBilin w (firstVector s q) = 0)
    (hw : (fixedQuadraticForm (s + 2) q).polarBilin w (secondVector s q) ≠ 0)
    (p : Parameters s q) :
    CommonNeighbours s q (standardPlane s q) (companionPlane s q w hws hwu hw) := by
  let R : SingularPlanes s q :=
    ⟨residualPlane s q w p, residualPlane_finrank s q w p, residualPlane_singular s q w p⟩
  have hd := residualPlane_common_neighbour_data s q w hws hwu hw p
  refine ⟨R, ⟨?_, hd.1.2⟩, ⟨?_, hd.2.2⟩⟩
  · intro he
    exact hd.1.1 (congrArg Subtype.val he)
  · intro he
    exact hd.2.1 (congrArg Subtype.val he)

theorem chartNeighbour_injective (s : ℕ) (q : CFSG.PrimePower) (w : fixedSpace (s + 2) q)
    (hws : fixedQuadraticForm (s + 2) q w = 0)
    (hwu : (fixedQuadraticForm (s + 2) q).polarBilin w (firstVector s q) = 0)
    (hw : (fixedQuadraticForm (s + 2) q).polarBilin w (secondVector s q) ≠ 0) :
    Function.Injective (chartNeighbour s q w hws hwu hw) := by
  intro p p' he
  exact residualPlane_injective s q w
    (congrArg (fun R : CommonNeighbours s q (standardPlane s q)
      (companionPlane s q w hws hwu hw) => R.val.val) he)

theorem normalized_commonNeighbours_card_lower (s : ℕ) (q : CFSG.PrimePower)
    (w : fixedSpace (s + 2) q)
    (hws : fixedQuadraticForm (s + 2) q w = 0)
    (hwu : (fixedQuadraticForm (s + 2) q).polarBilin w (firstVector s q) = 0)
    (hw : (fixedQuadraticForm (s + 2) q).polarBilin w (secondVector s q) ≠ 0) :
    q.order ^ (2 * (s + 1)) ≤ Nat.card
      (CommonNeighbours s q (standardPlane s q) (companionPlane s q w hws hwu hw)) := by
  have hc := Nat.card_le_card_of_injective (chartNeighbour s q w hws hwu hw)
    (chartNeighbour_injective s q w hws hwu hw)
  rw [parameters_card] at hc
  exact hc

end SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizedCommonNeighbours
