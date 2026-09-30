import SymmetricSubgroupAsymptotics.BinaryCarrierVaryingAxisRecovery

/-!
# Reconstruction across varying carrier words

The fixed-word transport is already injective.  The remaining source-code
issue is that the normal axes, and hence the quotient types, vary with the
actual source subgroup.  This file isolates the cross-word argument.

A bounded decoration records only the changed coordinates and their route
data.  On the other coordinates there is a fixed surjective evaluation from
the retained carrier to the original source group.  Equality of the final
ambient subgroups recovers the replacement kernels, so injectivity of comap
along evaluation recovers those unrecorded axes with fibre one.

The carrier family is kept literal throughout.  It may therefore contain
arbitrary nonabelian proper subdirect carriers on changed coordinates.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCrossVariableWordReconstruction

open SymmetricSubgroupAsymptotics

variable {ι X Decoration RouteData : Type*}
  [Finite ι] [DecidableEq ι]
  {U : ι → Type*} [∀ i, Group (U i)]
  {κ : ι → Type*} {V : ∀ i, κ i → Type*}
  [∀ i j, Group (V i j)]

/-- What equality of the bounded decoration is required to recover.  It
contains the axes on changed coordinates and the complete changed-route
code.  No unchanged-axis value occurs in this predicate. -/
def RecoversChangedData
    (changed : ι → Prop)
    (axis : X → ∀ i, Subgroup (U i))
    (route : X → RouteData)
    (decoration : X → Decoration) : Prop :=
  ∀ ⦃x y⦄, decoration x = decoration y →
    (∀ i, changed i → axis x i = axis y i) ∧ route x = route y

variable
  (C : ∀ i, Subgroup (∀ j, V i j))
  (source : X → Subgroup (∀ i, U i))
  (Q : X → ι → Type*) [∀ x i, Group (Q x i)]
  (α : ∀ x i, U i →* Q x i)
  (β : ∀ x i, C i →* Q x i)

/-- The actual final subgroup in the common displayed ambient word.  Its
type does not contain the varying quotient family. -/
def variableCarrierTarget (x : X) : Subgroup (∀ i j, V i j) :=
  carrierTransportInAmbient C (α x) (β x) (source x)

/-- Cross-variable reconstruction of every axis and the changed-route code.

The assumptions `sourceAxis` and `alphaKernel` say that the source relation
has the advertised exact axes.  On an unchanged coordinate, `identityKernel`
identifies the replacement kernel with the pullback of that axis along a
fixed surjective evaluation map.  Therefore no unchanged-axis tag is needed
in `decoration`. -/
theorem axes_routes_eq_of_decoration_target_eq
    (changed : ι → Prop)
    (axis : X → ∀ i, Subgroup (U i))
    (route : X → RouteData)
    (decoration : X → Decoration)
    (sourceAxis : ∀ x i, carrierAxis (source x) i = axis x i)
    (alphaKernel : ∀ x i, (α x i).ker = axis x i)
    (eval : ∀ i, ¬ changed i → C i →* U i)
    (evalSurjective : ∀ i hi, Function.Surjective (eval i hi))
    (identityKernel : ∀ x i (hi : ¬ changed i),
      (β x i).ker = (axis x i).comap (eval i hi))
    (changedData : RecoversChangedData changed axis route decoration)
    {x y : X} (hdecoration : decoration x = decoration y)
    (htarget : variableCarrierTarget C source Q α β x =
      variableCarrierTarget C source Q α β y) :
    (∀ i, axis x i = axis y i) ∧ route x = route y := by
  have hsourceX : ∀ i, carrierAxis (source x) i = (α x i).ker :=
    fun i => (sourceAxis x i).trans (alphaKernel x i).symm
  have hsourceY : ∀ i, carrierAxis (source y) i = (α y i).ker :=
    fun i => (sourceAxis y i).trans (alphaKernel y i).symm
  have hkernel : ∀ i, (β x i).ker = (β y i).ker := by
    apply carrierReplacement_kernels_eq_of_ambientTransport_eq
      (C := C) (α₁ := α x) (β₁ := β x)
      (α₂ := α y) (β₂ := β y)
      (H₁ := source x) (H₂ := source y) hsourceX hsourceY
    exact htarget
  have hchanged := changedData hdecoration
  refine ⟨?_,hchanged.2⟩
  intro i
  by_cases hi : changed i
  · exact hchanged.1 i hi
  · apply Subgroup.comap_injective (evalSurjective i hi)
    calc
      (axis x i).comap (eval i hi) = (β x i).ker :=
        (identityKernel x i hi).symm
      _ = (β y i).ker := hkernel i
      _ = (axis y i).comap (eval i hi) := identityKernel y i hi

/-- If the existing fixed-axis/fixed-route reconstruction recovers the
actual source once those data agree, then decoration together with the final
ambient subgroup is jointly injective across all varying words. -/
theorem decoration_target_injective
    (changed : ι → Prop)
    (axis : X → ∀ i, Subgroup (U i))
    (route : X → RouteData)
    (decoration : X → Decoration)
    (sourceAxis : ∀ x i, carrierAxis (source x) i = axis x i)
    (alphaKernel : ∀ x i, (α x i).ker = axis x i)
    (eval : ∀ i, ¬ changed i → C i →* U i)
    (evalSurjective : ∀ i hi, Function.Surjective (eval i hi))
    (identityKernel : ∀ x i (hi : ¬ changed i),
      (β x i).ker = (axis x i).comap (eval i hi))
    (changedData : RecoversChangedData changed axis route decoration)
    (fixedDataReconstruct : ∀ ⦃x y : X⦄,
      (∀ i, axis x i = axis y i) → route x = route y →
      variableCarrierTarget C source Q α β x =
        variableCarrierTarget C source Q α β y → x = y) :
    Function.Injective (fun x =>
      (decoration x,variableCarrierTarget C source Q α β x)) := by
  intro x y h
  have hdecoration : decoration x = decoration y := congrArg Prod.fst h
  have htarget : variableCarrierTarget C source Q α β x =
      variableCarrierTarget C source Q α β y := congrArg Prod.snd h
  obtain ⟨haxis,hroute⟩ := axes_routes_eq_of_decoration_target_eq
    C source Q α β changed axis route decoration sourceAxis alphaKernel
      eval evalSurjective identityKernel changedData hdecoration htarget
  exact fixedDataReconstruct haxis hroute htarget

/-- The fixed-data reconstruction hook has an unconditional carrier-level
implementation.  Once axes and route decoration have made `α`, `β`, and the
literal carriers fixed, the final ambient subgroup reconstructs the complete
source relation.  No fullness or commutativity of a retained carrier is
needed here. -/
theorem fixedCarrierTransport_injective
    {Q₀ : ι → Type*} [∀ i, Group (Q₀ i)]
    (α₀ : ∀ i, U i →* Q₀ i) (β₀ : ∀ i, C i →* Q₀ i)
    (β₀Surjective : ∀ i, Function.Surjective (β₀ i)) :
    Function.Injective
      (fun H : CarrierTransportSource α₀ =>
        carrierTransportInAmbient C α₀ β₀ H.1) := by
  intro H K h
  apply Subtype.ext
  have hH : ∀ i, (α₀ i).ker ≤ carrierAxis H.1 i :=
    fun i => (H.2.2 i).ge
  have hK : ∀ i, (α₀ i).ker ≤ carrierAxis K.1 i :=
    fun i => (K.2.2 i).ge
  let decode : Subgroup (∀ i j, V i j) → Subgroup (∀ i, U i) := fun J =>
    ((J.comap (carrierReplacementEmbedding C)).map
      (carrierProductMap β₀)).comap (carrierProductMap α₀)
  calc
    H.1 = decode (carrierTransportInAmbient C α₀ β₀ H.1) :=
      (carrierTransportInAmbient_reconstruct C α₀ β₀
        β₀Surjective H.1 hH).symm
    _ = decode (carrierTransportInAmbient C α₀ β₀ K.1) := congrArg decode h
    _ = K.1 := carrierTransportInAmbient_reconstruct C α₀ β₀
      β₀Surjective K.1 hK

/-! ## Assembly across decoration fibres -/

/-- The changed carriers themselves may vary with the decoration value.
It is enough to prove injectivity inside each fixed-decoration fibre, where
the preceding theorem applies with one literal carrier family.  Equality of
the first component first identifies the decoration values and hence the
carrier/route word; no comparison between different proper carriers is ever
required. -/
theorem sigmaDecoration_target_injective
    {D Y : Type*} {Fiber : D → Type*}
    (target : ∀ d, Fiber d → Y)
    (fiber_injective : ∀ d, Function.Injective (target d)) :
    Function.Injective
      (fun z : Σ d, Fiber d => (z.1,target z.1 z.2)) := by
  rintro ⟨d,x⟩ ⟨e,y⟩ h
  have hde : d = e := congrArg Prod.fst h
  subst e
  have hxy : x = y := fiber_injective d (congrArg Prod.snd h)
  subst y
  rfl

end SymmetricSubgroupAsymptotics.BinaryCarrierCrossVariableWordReconstruction
