import SymmetricSubgroupAsymptotics.BinaryCarrierCrossVariableWordReconstruction

/-!
# Reconstruction after aligning a varying carrier key

The ambient displayed product is fixed, but the quotient groups, quotient
maps, and literal proper carriers may vary with the source.  Package all data
which must first be aligned into one key.  Inside a fixed key fibre the
existing carrier reconstruction theorem is injective; adjoining the key to
the target therefore gives an injection on the dependent sum of all fibres.

For the physical source application the key can be the pair consisting of
the exact normal-axis family and the finite route datum.  Equality of axes
and routes then aligns every heterogeneous type before the fixed carrier
theorem is invoked.  No equality between carriers belonging to different
keys is required.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRouteIndexedReconstruction

open SymmetricSubgroupAsymptotics
open BinaryCarrierCrossVariableWordReconstruction

variable {ι Key : Type} [Finite ι] [DecidableEq ι]
  {U : ι → Type} [∀ i, Group (U i)]
  {κ : ι → Type} {V : ∀ i, κ i → Type}
  [∀ i j, Group (V i j)]
  (C : Key → ∀ i, Subgroup (∀ j, V i j))
  (Q : Key → ι → Type) [∀ r i, Group (Q r i)]
  (α : ∀ r i, U i →* Q r i)
  (β : ∀ r i, C r i →* Q r i)

/-- The complete source relation in one fixed carrier-data fibre. -/
abbrev KeySource (r : Key) : Type :=
  {H : Subgroup (∀ i, U i) // CarrierProductFull H ∧
    ∀ i, carrierAxis H i = (α r i).ker}

/-- The common-ambient target associated with one fixed carrier-data key. -/
def keyTarget (r : Key)
    (H : KeySource (U := U) (Q := Q) (α := α) r) :
    Subgroup (∀ i j, V i j) :=
  carrierTransportInAmbient (C r) (α r) (β r) H.1

/-- In one key fibre the common-ambient target recovers the complete source
relation.  This is the existing fixed-carrier theorem, with its dependence on
the key made explicit. -/
theorem keyTarget_injective
    (βSurjective : ∀ r i, Function.Surjective (β r i)) (r : Key) :
    Function.Injective (keyTarget C Q α β r) :=
  fixedCarrierTransport_injective (C r) (α r) (β r) (βSurjective r)

/-- Add the carrier-data key to the common ambient target.  Equality of the
first component puts both sources in the same dependent fibre; fixed-carrier
reconstruction then applies literally. -/
theorem sigmaKeyTarget_injective
    (βSurjective : ∀ r i, Function.Surjective (β r i)) :
    Function.Injective
      (fun z : Σ r : Key, KeySource (U := U) (Q := Q) (α := α) r =>
        (z.1,keyTarget C Q α β z.1 z.2)) := by
  exact sigmaDecoration_target_injective
    (target := keyTarget C Q α β)
    (keyTarget_injective C Q α β βSurjective)

/-- Any injective source code into the route-indexed source sigma remains
injective after replacing its source component by the common ambient carrier
target. -/
theorem encodedKeyTarget_injective
    {Actual : Type}
    (βSurjective : ∀ r i, Function.Surjective (β r i))
    (code : Actual → Σ r : Key,
      KeySource (U := U) (Q := Q) (α := α) r)
    (codeInjective : Function.Injective code) :
    Function.Injective
      (fun x => ((code x).1,keyTarget C Q α β (code x).1 (code x).2)) :=
  (sigmaKeyTarget_injective C Q α β βSurjective).comp codeInjective

/-- A direct adapter for the `fixedDataReconstruct` field of the physical
input.  The alignment hypotheses need only prove equality of the carrier
key.  The code records the original object as a source in the corresponding
key fibre. -/
theorem reconstruct_of_aligned_key
    {Actual RouteData : Type}
    (βSurjective : ∀ r i, Function.Surjective (β r i))
    (axis : Actual → ∀ i, Subgroup (U i))
    (route : Actual → RouteData)
    (key : Actual → Key)
    (word : ∀ x,
      KeySource (U := U) (Q := Q) (α := α) (key x))
    (codeInjective : Function.Injective
      (fun x => Sigma.mk (key x) (word x)))
    (alignKey : ∀ ⦃x y⦄,
      (∀ i, axis x i = axis y i) → route x = route y → key x = key y)
    ⦃x y : Actual⦄
    (haxis : ∀ i, axis x i = axis y i)
    (hroute : route x = route y)
    (htarget : keyTarget C Q α β (key x) (word x) =
      keyTarget C Q α β (key y) (word y)) :
    x = y := by
  apply encodedKeyTarget_injective C Q α β βSurjective
    (fun z => Sigma.mk (key z) (word z)) codeInjective
  exact Prod.ext (alignKey haxis hroute) htarget

/-! ## The standard axis/route key -/

/-- Axes and finite route data are precisely the information recovered before
the final fixed-data step in `FibreOnePhysicalInput`. -/
abbrev AxisRouteKey (RouteData : Type) :=
  (∀ i, Subgroup (U i)) × RouteData

/-- With the standard key `(axis, route)`, pointwise axis equality and route
equality discharge key alignment automatically.  A caller installs this
theorem as `fixedDataReconstruct`; its source, quotient maps, and carriers
should be the projections of `word` and the key-indexed data above. -/
theorem reconstruct_of_axis_route
    {Actual RouteData : Type}
    (C : AxisRouteKey (U := U) RouteData →
      ∀ i, Subgroup (∀ j, V i j))
    (Q : AxisRouteKey (U := U) RouteData → ι → Type)
    [∀ r i, Group (Q r i)]
    (α : ∀ r i, U i →* Q r i)
    (β : ∀ r i, C r i →* Q r i)
    (βSurjective : ∀ r i, Function.Surjective (β r i))
    (axis : Actual → ∀ i, Subgroup (U i))
    (route : Actual → RouteData)
    (word : ∀ x, KeySource (U := U) (Q := Q) (α := α)
      (axis x,route x))
    (codeInjective : Function.Injective
      (fun x => Sigma.mk (axis x,route x) (word x)))
    ⦃x y : Actual⦄
    (haxis : ∀ i, axis x i = axis y i)
    (hroute : route x = route y)
    (htarget : keyTarget C Q α β (axis x,route x) (word x) =
      keyTarget C Q α β (axis y,route y) (word y)) :
    x = y := by
  apply reconstruct_of_aligned_key C Q α β βSurjective axis route
    (fun z => (axis z,route z)) word codeInjective
    (fun {_ _} haxis' hroute' => Prod.ext (funext haxis') hroute')
    haxis hroute htarget

end SymmetricSubgroupAsymptotics.BinaryCarrierRouteIndexedReconstruction
