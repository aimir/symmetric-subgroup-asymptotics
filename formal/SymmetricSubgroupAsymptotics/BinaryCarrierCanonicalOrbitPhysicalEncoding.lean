import SymmetricSubgroupAsymptotics.BinaryDegreeEightPhysicalDecoration
import SymmetricSubgroupAsymptotics.BinaryCarrierCrossVariableWordReconstruction
import SymmetricSubgroupAsymptotics.BinaryCarrierRoutedProfileAxisClosure
import SymmetricSubgroupAsymptotics.BinaryCarrierSourceExtraction
import SymmetricSubgroupAsymptotics.OrbitProfileFromOrbits

/-!
# Canonical orbit words and physical reconstruction

The first half of this file performs the source-side construction which is
already unconditional.  A canonical simultaneous orbit decomposition gives
a full subgroup of the product of its literal orbit images.  Flattening that
product, taking its literal coordinate axes, and choosing one `AxisSlot` per
orbit occurrence produces the exact dependent `WordSource` consumed by the
variable-word producer.

The second half isolates cross-chart reconstruction.  Equal explicit block
decorations align every changed carrier coordinate.  Equality of the final
physical targets is required only to reflect equality of the corresponding
literal simultaneous carrier transports.  The checked identity-carrier
pullback theorem then recovers every unchanged normal axis with fibre one;
fixed-data reversibility recovers the original source.  This produces a
`PhysicalEncoding` and hence the bounded retained-bin estimate without a raw
profile sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalOrbitPhysicalEncoding

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierActualDecoratedTransport
open BinaryCarrierCrossVariableWordReconstruction
open BinaryCarrierDependentVariableWordProducer
open BinaryCarrierMixtureCompletion
open BinaryCarrierParameterProfiles
open BinaryCarrierProfileTransport
open BinaryCarrierRoutedProfileAxisClosure
open BinaryCarrierRoutedWordClosure
open BinaryCarrierSourceExtraction
open BinaryCarrierWordClosure
open BinaryDegreeEightPhysicalAnalyticClosure
open BinaryDegreeEightPhysicalDecoration

/-! ## A routed source from the canonical complete orbit chart -/

namespace CanonicalOrbitWord

variable {ι X : Type} [Fintype ι] [DecidableEq ι] [Finite X]
  (Ω : ι → Type) [∀ i, Fintype (Ω i)]
  (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
  (H : Subgroup (Equiv.Perm X))
  (C : OrbitProfileFromOrbits.Data H U)

/-- Put the actual subgroup on the simultaneous canonical orbit chart. -/
def model : Subgroup (Equiv.Perm (OrbitProfilePoints Ω C.multiplicity)) :=
  relabelSubgroup C.chart.symm H

theorem model_fullOn :
    OrbitProfileFullOn U (Equiv.refl _) (model Ω U H C) := by
  have h := C.chart_full.relabel C.chart.symm
  simpa only [Equiv.self_trans_symm] using h

theorem model_full : OrbitProfileFull U 1 (model Ω U H C) :=
  (orbitProfileFullOn_iff U (Equiv.refl _) (model Ω U H C)).mp
    (model_fullOn Ω U H C)

/-- The complete correlated subgroup of the product of all literal orbit
images. -/
def profileSource :
    Subgroup (OrbitProfileProductGroup C.multiplicity U) :=
  (model Ω U H C).comap
    (orbitProfileProductAction C.multiplicity U)

theorem profileSource_full :
    OrbitProfileProductFull C.multiplicity U (profileSource Ω U H C) :=
  orbitProfileFull_comap (model_full Ω U H C)

/-- Flatten the curried orbit profile to one coordinate per literal orbit. -/
def flatSource : Subgroup (∀ o : (Σ i, Fin (C.multiplicity i)), U o.1) :=
  (profileSource Ω U H C).map
    (flatten Ω U C.multiplicity).toMonoidHom

theorem flatSource_full : CarrierProductFull (flatSource Ω U H C) :=
  (full_flatten_iff Ω U C.multiplicity (profileSource Ω U H C)).mp
    (profileSource_full Ω U H C)

/-- The literal normal axis on one actual orbit coordinate. -/
def axis (o : (Σ i, Fin (C.multiplicity i))) : Subgroup (U o.1) :=
  carrierAxis (flatSource Ω U H C) o

theorem axis_normal (o : (Σ i, Fin (C.multiplicity i))) :
    (axis Ω U H C o).Normal :=
  carrierAxis_normal (flatSource Ω U H C) (flatSource_full Ω U H C) o

variable (R : ∀ o : (Σ i, Fin (C.multiplicity i)),
  AxisSlot (U o.1) (axis Ω U H C o))

/-- The exact-axis product cell associated to the actual subgroup. -/
def exactAxisFamily :
    BinaryCarrierRoutedWordClosure.ExactAxisFamily
      (fun o : (Σ i, Fin (C.multiplicity i)) => U o.1) (axis Ω U H C) :=
  ⟨flatSource Ω U H C, flatSource_full Ω U H C, fun _ => rfl⟩

/-- The complete carrier source.  All correlations between distinct original
orbits are retained in its underlying subgroup. -/
def sourceAt :
    CarrierTransportSource
      (alphas (fun o : (Σ i, Fin (C.multiplicity i)) => (R o).slot)) :=
  routedSource (fun o : (Σ i, Fin (C.multiplicity i)) => U o.1)
    (axis Ω U H C) R
    (exactAxisFamily Ω U H C)

/-- Bundle the possibly heterogeneous orbit routes as one dependent word. -/
def slotWord : SlotWord where
  Index := Σ i, Fin (C.multiplicity i)
  indexFintype := inferInstance
  indexDecidableEq := Classical.decEq _
  slot := fun o => (R o).slot

/-- Install the common numerical parameter and retention data. -/
def routedWord {N Cold : ℕ}
    (hparameter : (slotWord Ω U H C R).parameter = N)
    (hnoncritical : (slotWord Ω U H C R).HasNoncritical)
    (hretention : (slotWord Ω U H C R).RetentionAt Cold) :
    RoutedWord N Cold :=
  RoutedWord.ofSlotWord (slotWord Ω U H C R)
    hparameter hnoncritical hretention

end CanonicalOrbitWord

/-! ## Recovering a physical encoding from the fibre-one theorem -/

/-- A blockwise physical target reflects its literal ambient value as soon as
the block decoration is fixed.  This is the small categorical fact needed by
the cross-chart reconstruction: the physical realization is allowed to use a
different chart for each decoration, but no comparison between two such
charts is required. -/
theorem ambient_eq_of_blockwise_target_eq
    {Actual Decoration Ambient Physical : Type*}
    (blocks : Actual → Decoration)
    (ambient : Actual → Ambient)
    (target : Actual → Physical)
    (physicalize : Decoration → Ambient → Physical)
    (target_eq : ∀ x, target x = physicalize (blocks x) (ambient x))
    (physicalize_injective : ∀ d, Function.Injective (physicalize d))
    {x y : Actual}
    (hblocks : blocks x = blocks y)
    (htarget : target x = target y) :
    ambient x = ambient y := by
  apply physicalize_injective (blocks x)
  have hphysical :
      physicalize (blocks x) (ambient x) =
        physicalize (blocks y) (ambient y) := by
    calc
      physicalize (blocks x) (ambient x) = target x := (target_eq x).symm
      _ = target y := htarget
      _ = physicalize (blocks y) (ambient y) := target_eq y
  rw [← hblocks] at hphysical
  exact hphysical

/-- Insert one literal physical parameter bin into the common retained-bin
target.  This is the last, manifestly injective, step after a fixed
`ProfileDisplay.physicalTarget` has produced the subgroup in that bin. -/
def retainedBinTarget {N Cold : ℕ} (b : RetainedBin N Cold) :
    PhysicalFamily
        (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N)) →
      Target N Cold := fun H ↦ ⟨b,H⟩

theorem retainedBinTarget_injective {N Cold : ℕ}
    (b : RetainedBin N Cold) :
    Function.Injective (retainedBinTarget b) := by
  intro H K h
  exact (@sigma_mk_injective
    (RetainedBin N Cold)
    (fun c ↦ PhysicalFamily
      (N - binSupport c.1) c.1.1.1 c.1.1.2 (Fin (2 * N))) b) h

/-- Specialization of `ambient_eq_of_blockwise_target_eq` to the literal
simultaneous carrier subgroup.  In an application, `physicalize d` is the
fixed profile-display/action/relabel map determined by the mixed block table
`d`.  Its injectivity is precisely the fixed-chart injectivity already used
by `physicalTransport_injective`.

This formulation is deliberately blockwise: equality of a physical subgroup
need not compare two unrelated choices of profile display. -/
theorem variableCarrierTarget_eq_of_blockwise_target_eq
    {Actual : Type*} {N Cold : ℕ}
    {I : Type*} [Finite I] [DecidableEq I]
    {U : I → Type*} [∀ i, Group (U i)]
    {kappa : I → Type*} {V : ∀ i, kappa i → Type*}
    [∀ i j, Group (V i j)]
    {Q : Actual → I → Type*} [∀ x i, Group (Q x i)]
    (C : ∀ i, Subgroup (∀ j, V i j))
    (source : Actual → Subgroup (∀ i, U i))
    (alpha : ∀ x i, U i →* Q x i)
    (beta : ∀ x i, C i →* Q x i)
    (blocks : Actual → CanonicalBlockTable N Cold)
    (target : Actual → Target N Cold)
    (physicalize : CanonicalBlockTable N Cold →
      Subgroup (∀ i j, V i j) → Target N Cold)
    (target_eq : ∀ x, target x = physicalize (blocks x)
      (variableCarrierTarget C source Q alpha beta x))
    (physicalize_injective : ∀ d, Function.Injective (physicalize d))
    {x y : Actual}
    (hblocks : blocks x = blocks y)
    (htarget : target x = target y) :
    variableCarrierTarget C source Q alpha beta x =
      variableCarrierTarget C source Q alpha beta y :=
  ambient_eq_of_blockwise_target_eq blocks
    (variableCarrierTarget C source Q alpha beta) target physicalize
    target_eq physicalize_injective hblocks htarget

/-- Version adapted to `ProfileDisplay.physicalTarget`.  The fixed-chart map
is naturally defined on full displayed ambient subgroups, so the fullness
proof is bundled before applying blockwise injectivity and forgotten again
afterwards. -/
theorem variableCarrierTarget_eq_of_blockwise_full_target_eq
    {Actual : Type*} {N Cold : ℕ}
    {I : Type*} [Finite I] [DecidableEq I]
    {U : I → Type*} [∀ i, Group (U i)]
    {kappa : I → Type*} {V : ∀ i, kappa i → Type*}
    [∀ i j, Group (V i j)]
    {Q : Actual → I → Type*} [∀ x i, Group (Q x i)]
    (C : ∀ i, Subgroup (∀ j, V i j))
    (source : Actual → Subgroup (∀ i, U i))
    (alpha : ∀ x i, U i →* Q x i)
    (beta : ∀ x i, C i →* Q x i)
    (ambientFull : ∀ x, CarrierDisplayedFull
      (variableCarrierTarget C source Q alpha beta x))
    (blocks : Actual → CanonicalBlockTable N Cold)
    (target : Actual → Target N Cold)
    (physicalize : CanonicalBlockTable N Cold →
      CarrierTransportTarget (V := V) → Target N Cold)
    (target_eq : ∀ x, target x = physicalize (blocks x)
      ⟨variableCarrierTarget C source Q alpha beta x, ambientFull x⟩)
    (physicalize_injective : ∀ d, Function.Injective (physicalize d))
    {x y : Actual}
    (hblocks : blocks x = blocks y)
    (htarget : target x = target y) :
    variableCarrierTarget C source Q alpha beta x =
      variableCarrierTarget C source Q alpha beta y := by
  have hfull :
      (⟨variableCarrierTarget C source Q alpha beta x, ambientFull x⟩ :
          CarrierTransportTarget (V := V)) =
        ⟨variableCarrierTarget C source Q alpha beta y, ambientFull y⟩ :=
    ambient_eq_of_blockwise_target_eq blocks
      (fun z ↦
        (⟨variableCarrierTarget C source Q alpha beta z, ambientFull z⟩ :
          CarrierTransportTarget (V := V)))
      target physicalize target_eq physicalize_injective hblocks htarget
  exact congrArg Subtype.val hfull

/-- A total inverse on the range of an injective map.  The `Nonempty`
assumption is needed only away from the range; every value used by the
physical encoding lies in the range. -/
def inverseOfInjective {A B : Type*} [Nonempty A]
    (f : A → B) (y : B) : A :=
  if h : ∃ x, f x = y then Classical.choose h else Classical.choice inferInstance

theorem inverseOfInjective_apply {A B : Type*} [Nonempty A]
    (f : A → B) (hf : Function.Injective f) (x : A) :
    inverseOfInjective f (f x) = x := by
  unfold inverseOfInjective
  split
  · rename_i h
    apply hf
    exact Classical.choose_spec h
  · rename_i h
    exact False.elim (h ⟨x,rfl⟩)

/-- Any jointly injective block-table/target map supplies the total recovery
operation expected by `PhysicalEncoding`. -/
def physicalEncodingOfJointInjective
    {Actual : Type*} [Nonempty Actual] {N Cold : ℕ} {hN : 4 ≤ N}
    (blocks : Actual → CanonicalBlockTable N Cold)
    (target : Actual → Target N Cold)
    (hinjective : Function.Injective (fun x => (blocks x,target x))) :
    PhysicalEncoding Actual N Cold hN where
  blocks := blocks
  target := target
  recover := fun d t => inverseOfInjective (fun x => (blocks x,target x)) (d,t)
  recover_encode := fun x =>
    inverseOfInjective_apply (fun z => (blocks z,target z)) hinjective x

/-- The exact cross-chart hypotheses not supplied by the one-subgroup orbit
construction above.

The unchanged coordinates are required to be literal identity carriers:
`identityKernel` expresses their replacement kernels as pullbacks along a
fixed surjective evaluation.  Thus the checked comap-injectivity theorem
recovers those axes rather than charging them to the block decoration. -/
structure FibreOnePhysicalInput
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
  blocks : Actual → CanonicalBlockTable N Cold
  target : Actual → Target N Cold
  sourceAxis : ∀ x i, carrierAxis (source x) i = axis x i
  alphaKernel : ∀ x i, (alpha x i).ker = axis x i
  eval : ∀ i, ¬ changed i → C i →* U i
  evalSurjective : ∀ i hi, Function.Surjective (eval i hi)
  identityKernel : ∀ x i (hi : ¬ changed i),
    (beta x i).ker = (axis x i).comap (eval i hi)
  blocksChangedData :
    RecoversChangedData changed axis route blocks
  targetReflectsAmbient : ∀ {x y}, blocks x = blocks y → target x = target y →
    variableCarrierTarget C source Q alpha beta x =
      variableCarrierTarget C source Q alpha beta y
  fixedDataReconstruct : ∀ ⦃x y : Actual⦄,
    (∀ i, axis x i = axis y i) → route x = route y →
    variableCarrierTarget C source Q alpha beta x =
      variableCarrierTarget C source Q alpha beta y → x = y

namespace FibreOnePhysicalInput

variable {Actual RouteData : Type*} {N Cold : ℕ}
  {I : Type*} [Finite I] [DecidableEq I]
  {U : I → Type*} [∀ i, Group (U i)]
  {κ : I → Type*} {V : ∀ i, κ i → Type*} [∀ i j, Group (V i j)]
  {Q : Actual → I → Type*} [∀ x i, Group (Q x i)]
  {C : ∀ i, Subgroup (∀ j, V i j)}
  (P : FibreOnePhysicalInput Actual RouteData N Cold I U κ V Q C)

/-- Block decoration plus the common physical target is injective.  The proof
first invokes exact replacement-kernel recovery, including fibre-one recovery
of every unchanged identity axis, and then the fixed-data inverse. -/
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
  exact P.fixedDataReconstruct haxis hroute hambient

/-- The complete physical encoding obtained from the canonical block table,
the simultaneous carrier target, and unchanged-axis fibre-one recovery. -/
def toPhysicalEncoding [Nonempty Actual] {hN : 4 ≤ N} :
    PhysicalEncoding Actual N Cold hN :=
  physicalEncodingOfJointInjective P.blocks P.target P.blocks_target_injective

/-- Consequently the whole finite retained-background sector has one bounded
block-decoration factor and the exact retained-bin sum. -/
theorem card_le_bound_mul_sum
    (P : FibreOnePhysicalInput Actual RouteData N Cold I U κ V Q C)
    [Nonempty Actual] [Finite Actual]
    {hN : 4 ≤ N} :
    Nat.card Actual ≤
      (2 * N + 2) ^ (6 * (2 * Cold)) *
        ∑ b : RetainedBin N Cold,
          Nat.card (PhysicalFamily
            (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) :=
  BinaryDegreeEightPhysicalDecoration.PhysicalEncoding.card_le_bound_mul_sum
    (hN := hN) (toPhysicalEncoding (hN := hN) P)

end FibreOnePhysicalInput

end SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalOrbitPhysicalEncoding
