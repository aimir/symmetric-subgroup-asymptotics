import SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalOrbitPhysicalEncoding
import SymmetricSubgroupAsymptotics.BinaryDegreeEightSixteenPhysicalEncoding

/-!
# Intrinsic-target reconstruction for the mixed carrier word

The mixed degree-eight/degree-sixteen decoration intentionally omits charts
on unchanged critical and cyclic-four identity cells.  Consequently the
block table alone does not determine the complete physical display.  The
correct incidence theorem also uses the final physical target itself as an
intrinsic presentation key.

For each fixed pair consisting of a mixed table and an intrinsic target key,
the physical realization must be injective on the literal displayed carrier
subgroup.  Equality of two targets then aligns that key automatically.  The
usual fibre-one kernel argument recovers all axes omitted from the table,
and a final source reconstruction recovers the actual labelled subgroup.

This formulation keeps arbitrary nonabelian proper subdirect carrier cells:
no factorization of their internal subgroup relation is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMixedFibreOnePhysicalEncoding

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedTransport
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierCrossVariableWordReconstruction
open BinaryCarrierProfileTransport
open BinaryDegreeEightSixteenPhysicalDecoration
open BinaryDegreeEightSixteenPhysicalEncoding

/-- If the chosen physical realization is injective after fixing both the
bounded decoration and an intrinsic key extracted from the target itself,
then equal decorations and equal targets recover the ambient object. -/
theorem ambient_eq_of_intrinsic_target_eq
    {Actual Decoration Ambient Physical : Type*}
    (blocks : Actual → Decoration)
    (ambient : Actual → Ambient)
    (target : Actual → Physical)
    (physicalize : Decoration → Physical → Ambient → Physical)
    (target_eq : ∀ x,
      target x = physicalize (blocks x) (target x) (ambient x))
    (physicalize_injective : ∀ d p, Function.Injective (physicalize d p))
    {x y : Actual}
    (hblocks : blocks x = blocks y)
    (htarget : target x = target y) :
    ambient x = ambient y := by
  apply physicalize_injective (blocks x) (target x)
  have hphysical :
      physicalize (blocks x) (target x) (ambient x) =
        physicalize (blocks y) (target y) (ambient y) := by
    calc
      physicalize (blocks x) (target x) (ambient x) = target x :=
        (target_eq x).symm
      _ = target y := htarget
      _ = physicalize (blocks y) (target y) (ambient y) := target_eq y
  rw [← hblocks, ← htarget] at hphysical
  exact hphysical

/-- Complete direct-incidence input for the mixed retained-background word.

`physicalize` is indexed by the target itself.  In the application this key
supplies its retained bin and a canonical complete orbit presentation,
including the unchanged identity cells which are absent from `blocks`.
The last field is the direct labelled-source inverse after all axes, route
data, and the common carrier ambient have been recovered. -/
structure Input
    (Actual RouteData : Type*) (N Cold : ℕ)
    (I : Type*) [Finite I] [DecidableEq I]
    (U : I → Type*) [∀ i, Group (U i)]
    (κ : I → Type*) (V : ∀ i, κ i → Type*) [∀ i j, Group (V i j)]
    (Q : Actual → I → Type*) [∀ x i, Group (Q x i)]
    (C : ∀ i, Subgroup (∀ j, V i j)) where
  changed : I → Prop
  source : Actual → Subgroup (∀ i, U i)
  axis : Actual → ∀ i, Subgroup (U i)
  route : Actual → RouteData
  alpha : ∀ x i, U i →* Q x i
  beta : ∀ x i, C i →* Q x i
  blocks : Actual → CanonicalMixedBlockTable N Cold
  target : Actual → Target N Cold
  sourceAxis : ∀ x i, carrierAxis (source x) i = axis x i
  alphaKernel : ∀ x i, (alpha x i).ker = axis x i
  eval : ∀ i, ¬ changed i → C i →* U i
  evalSurjective : ∀ i hi, Function.Surjective (eval i hi)
  identityKernel : ∀ x i (hi : ¬ changed i),
    (beta x i).ker = (axis x i).comap (eval i hi)
  blocksChangedData :
    RecoversChangedData changed axis route blocks
  ambientFull : ∀ x, CarrierDisplayedFull
    (variableCarrierTarget C source Q alpha beta x)
  physicalize : CanonicalMixedBlockTable N Cold → Target N Cold →
    CarrierTransportTarget (V := V) → Target N Cold
  targetFactor : ∀ x, target x = physicalize (blocks x) (target x)
    ⟨variableCarrierTarget C source Q alpha beta x, ambientFull x⟩
  physicalizeInjective : ∀ d t, Function.Injective (physicalize d t)
  sourceReconstruct : ∀ ⦃x y : Actual⦄,
    blocks x = blocks y → target x = target y →
    (∀ i, axis x i = axis y i) → route x = route y →
    variableCarrierTarget C source Q alpha beta x =
      variableCarrierTarget C source Q alpha beta y → x = y

namespace Input

variable {Actual RouteData : Type*} {N Cold : ℕ}
  {I : Type*} [Finite I] [DecidableEq I]
  {U : I → Type*} [∀ i, Group (U i)]
  {κ : I → Type*} {V : ∀ i, κ i → Type*} [∀ i j, Group (V i j)]
  {Q : Actual → I → Type*} [∀ x i, Group (Q x i)]
  {C : ∀ i, Subgroup (∀ j, V i j)}
  (P : Input Actual RouteData N Cold I U κ V Q C)

/-- Equal mixed decorations and equal final targets recover the literal
simultaneous carrier subgroup. -/
theorem targetReflectsAmbient {x y : Actual}
    (hblocks : P.blocks x = P.blocks y)
    (htarget : P.target x = P.target y) :
    variableCarrierTarget C P.source Q P.alpha P.beta x =
      variableCarrierTarget C P.source Q P.alpha P.beta y := by
  have hfull :
      (⟨variableCarrierTarget C P.source Q P.alpha P.beta x,
          P.ambientFull x⟩ : CarrierTransportTarget (V := V)) =
        ⟨variableCarrierTarget C P.source Q P.alpha P.beta y,
          P.ambientFull y⟩ :=
    ambient_eq_of_intrinsic_target_eq P.blocks
      (fun z =>
        (⟨variableCarrierTarget C P.source Q P.alpha P.beta z,
            P.ambientFull z⟩ : CarrierTransportTarget (V := V)))
      P.target P.physicalize P.targetFactor P.physicalizeInjective
      hblocks htarget
  exact congrArg Subtype.val hfull

/-- The direct mixed incidence hypotheses imply the joint injection required
by the `K = 10` physical encoder. -/
theorem blocks_target_injective :
    Function.Injective (fun x => (P.blocks x,P.target x)) := by
  intro x y h
  have hblocks : P.blocks x = P.blocks y := congrArg Prod.fst h
  have htarget : P.target x = P.target y := congrArg Prod.snd h
  have hambient := P.targetReflectsAmbient hblocks htarget
  obtain ⟨haxis,hroute⟩ :=
    axes_routes_eq_of_decoration_target_eq
      C P.source Q P.alpha P.beta P.changed P.axis P.route P.blocks
      P.sourceAxis P.alphaKernel P.eval P.evalSurjective P.identityKernel
      P.blocksChangedData hblocks hambient
  exact P.sourceReconstruct hblocks htarget haxis hroute hambient

/-- Package the direct incidence theorem as the mixed physical encoder. -/
def toPhysicalEncoding {hN : 4 ≤ N} :
    BinaryDegreeEightSixteenPhysicalEncoding.PhysicalEncoding
      Actual N Cold hN where
  blocks := P.blocks
  target := P.target
  joint_injective := P.blocks_target_injective

/-- Exact cardinal consequence of the mixed direct-incidence theorem. -/
theorem card_le_bound_mul_sum [Finite Actual] {hN : 4 ≤ N}
    (P : Input Actual RouteData N Cold I U κ V Q C) :
    Nat.card Actual ≤
      (2 * N + 2) ^ (10 * (2 * Cold)) *
        ∑ b : RetainedBin N Cold,
          Nat.card (BinaryCarrierParameterProfiles.PhysicalFamily
            (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) :=
  BinaryDegreeEightSixteenPhysicalEncoding.PhysicalEncoding.card_le_bound_mul_sum
    (toPhysicalEncoding (hN := hN) P)

end Input

end SymmetricSubgroupAsymptotics.BinaryCarrierMixedFibreOnePhysicalEncoding
