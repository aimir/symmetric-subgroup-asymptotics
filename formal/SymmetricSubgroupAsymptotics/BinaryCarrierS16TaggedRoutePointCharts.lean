import SymmetricSubgroupAsymptotics.BinaryCarrierS16TaggedPositiveRoutes
import SymmetricSubgroupAsymptotics.BinaryCarrierFusionNaturalPointChart

/-!
# Point charts retained by the tagged positive S16 routes

The tagged route packages already keep the finite branch, registry
conjugacy, and exact certified slot in one Type-valued object.  This file
keeps the corresponding point-level correlation: the displayed points of
that exact slot are identified with the points of its original source
action.

For one-cell routes this only removes the unique cell coordinate before
applying the fixed catalogue chart and the retained conjugacy.  The proper
`16T1086` route has four displayed cells; its checked exact physical-profile
chart assembles those cells without replacing their proper subdirect
carrier by a product.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierS16TaggedPositiveRoutes

open SymmetricSubgroupAsymptotics
open BinaryCarrierFusionNaturalPointChart
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure
open BinaryDegreeEightBaseRoutes

/-- The point set displayed by one bundled carrier slot. -/
abbrev DisplayedPoints (S : Slot) :=
  Σ c : S.Cells, mixturePoints (S.color c)

namespace DegreeFourRoute

variable {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
  {W : BinaryS16CanonicalCarrierProfile.SmallOrbitWitness 4 H}

/-- The one displayed regular-C4 cell, on the exact chart retained by the
same width-four route, is the original four-point source action. -/
def displayedPointEquiv (R : DegreeFourRoute W) :
    DisplayedPoints R.certified.axisSlot.slot ≃ Fin 4 := by
  rcases R with ⟨e,action_eq⟩
  change (Σ _ : Fin 1, mixturePoints (.inr none)) ≃ Fin 4
  exact (Equiv.uniqueSigma _).trans e

end DegreeFourRoute

namespace DegreeEightRoute

variable {U : Subgroup (Equiv.Perm (Fin 8))}
  {N : Subgroup U} [N.Normal]

/-- Every positive degree-eight route displays one cell.  A base route first
uses its fixed mixture-colour-to-registry chart; an exceptional route already
displays the literal `8T27` point set.  The retained conjugacy then returns
registry labels to the original source labels. -/
def displayedPointEquiv (R : DegreeEightRoute U N) :
    DisplayedPoints R.certified.axisSlot.slot ≃ Fin 8 := by
  cases R with
  | base b hb t kind g hg =>
      change (Σ _ : Fin 1, mixturePoints (baseKind b)) ≃ Fin 8
      exact (Equiv.uniqueSigma _).trans
        ((basePointEquiv b).trans g.symm)
  | t16 i g hg source axis =>
      change (Σ _ : Fin 1, Fin 8) ≃ Fin 8
      exact (Equiv.uniqueSigma _).trans g.symm
  | t20 i g hg source axis =>
      change (Σ _ : Fin 1, Fin 8) ≃ Fin 8
      exact (Equiv.uniqueSigma _).trans g.symm
  | t21 i g hg source axis =>
      change (Σ _ : Fin 1, Fin 8) ≃ Fin 8
      exact (Equiv.uniqueSigma _).trans g.symm

end DegreeEightRoute

namespace DegreeSixteenRoute

variable {U : Subgroup (Equiv.Perm (Fin 16))}
  {N : Subgroup U} [N.Normal]

/-- Every positive degree-sixteen route recovers its original sixteen-point
source labels.  The unchanged `16T1332` route removes one cell coordinate.
For the proper `16T1086` route, the occurrence/point sigma is first rebuilt
as the exact one-C4/three-D8 model, then sent through its checked physical
chart.  The final retained conjugacy returns catalogue labels to the actual
source labels in both branches. -/
def displayedPointEquiv (R : DegreeSixteenRoute U N) :
    DisplayedPoints R.certified.axisSlot.slot ≃ Fin 16 := by
  cases R with
  | t1086 g hg owner physical =>
      change
        (Σ c : BinaryExceptional16ProfileCarrier.Occurrence,
          mixturePoints c.1) ≃ Fin 16
      exact ((profilePointEquivOccurrencePoint
        BinaryExceptional16PhysicalProfile.ExactProfile.pointFamily
        BinaryExceptional16PhysicalProfile.ExactProfile.multiplicity).symm.trans
          BinaryExceptional16PhysicalProfile.ExactProfile.chart).trans g.symm
  | t1332 g hg row physical =>
      change (Σ _ : Fin 1, Fin 16) ≃ Fin 16
      exact (Equiv.uniqueSigma _).trans g.symm

end DegreeSixteenRoute

end SymmetricSubgroupAsymptotics.BinaryCarrierS16TaggedPositiveRoutes

end
