import SymmetricSubgroupAsymptotics.ActualWreathComplementMonomialCoordinates
import SymmetricSubgroupAsymptotics.ActualWreathComplementFullRoot
import SymmetricSubgroupAsymptotics.TwistedMonomialCocycleFilteredFrame

/-! The actual full-component complement family has a twisted frame/root
code. Its action and coefficient twists are constructed from the SAME
literal kernel chart and wreath map. The baseline is chosen inside that
full family, so its local and outer maps are genuinely onto. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathFullComplementFrameBound
open ActualComplementCocycleChartTransport ActualComplementFullRootComponent
open ActualWreathComplementMonomialCoordinates TwistedMonomialCocycleFrame

variable {E Q R X A D : Type} [Group E] [Group Q] [Group R] [Group A] [Group D]
    [MulAction Q X] [MulAction R X]
variable (π : E →* Q) (e : π.ker ≃* (X → A))
    (ξ : E →* PermutationalWreathProduct D R X) (ι : A →* D)
    (C : Chart π e ξ ι) (x0 : X)
    (L0 : ActualWreathComplementFullRoot.FullFamily π ξ)

abbrev action : Q →* MulAut (X → A) := coordinateAction π L0.val e

abbrev theta : Q → X → MulAut A := actualTwist π e ξ ι L0.val C

theorem coordinateLaw (q : Q) (f : X → A) (x : X) :
    (action π e ξ L0 q f) (q • x)=theta π e ξ ι C L0 q x (f x) :=
  monomial_law π e ξ ι L0.val C q f x

abbrev rootAction : MulAction.stabilizer Q x0 →* MulAut A :=
  TwistedMonomialCocycleFrame.rootAction (action π e ξ L0)
    (theta π e ξ ι C L0) (coordinateLaw π e ξ ι C L0) x0

abbrev localBase : MulAction.stabilizer Q x0 →* D :=
  localHom π x0 (ActualWreathComplementFullRoot.component π ξ C.top_compatible x0) L0.val

theorem root_compatible (h : MulAction.stabilizer Q x0) (a : A) :
    ι (rootAction π e ξ ι C x0 L0 h a)=
      localBase π e ξ ι C x0 L0 h*ι a*(localBase π e ξ ι C x0 L0 h)⁻¹ :=
  root_action_compatible π x0
    (ActualWreathComplementFullRoot.component π ξ C.top_compatible x0)
    L0.val e ι (fun n => (C.coordinate_compatible n x0).symm)
    (theta π e ξ ι C L0) (coordinateLaw π e ξ ι C L0) h a

/-- Only root cocycles with onto actual local homomorphism are counted. -/
abbrev FullRoot := TwistedSimpleRootCocycleCount.FullRoot
  (rootAction π e ξ ι C x0 L0) (localBase π e ξ ι C x0 L0) ι
  (root_compatible π e ξ ι C x0 L0)

def familyCode : ActualWreathComplementFullRoot.FullFamily π ξ →
    {c : Cocycle (action π e ξ L0) // Function.Surjective
      (TwistedCocycleAssociatedHom.associatedHom
        (rootAction π e ξ ι C x0 L0) (localBase π e ξ ι C x0 L0) ι
        (root_compatible π e ξ ι C x0 L0)
        (rootRestriction (action π e ξ L0) (theta π e ξ ι C L0)
          (coordinateLaw π e ξ ι C L0) x0 c))} :=
  ActualWreathComplementFullRoot.fullComponentCode π ξ C.top_compatible x0 L0.val e ι
    (fun n => (C.coordinate_compatible n x0).symm)
    (theta π e ξ ι C L0) (coordinateLaw π e ξ ι C L0)

theorem familyCode_injective : Function.Injective (familyCode π e ξ ι C x0 L0) :=
  ActualWreathComplementFullRoot.fullComponentCode_injective π ξ C.top_compatible x0
    L0.val e ι (fun n => (C.coordinate_compatible n x0).symm)
    (theta π e ξ ι C L0) (coordinateLaw π e ξ ι C L0)

/-- No independent monomial-action or full-root hypothesis is supplied. -/
theorem card_le_frame_root [Finite Q] [Finite X] [Finite A]
    [MulAction.IsPretransitive Q X] :
    Nat.card (ActualWreathComplementFullRoot.FullFamily π ξ) ≤
      Nat.card A ^ Nat.card X * Nat.card (FullRoot π e ξ ι C x0 L0) := by
  have hi := Nat.card_le_card_of_injective (familyCode π e ξ ι C x0 L0)
    (familyCode_injective π e ξ ι C x0 L0)
  have hf := TwistedMonomialCocycleFilteredFrame.card_le_transitive_filtered
    (action π e ξ L0) (theta π e ξ ι C L0) (coordinateLaw π e ξ ι C L0) x0
    (fun r => Function.Surjective
      (TwistedCocycleAssociatedHom.associatedHom
        (rootAction π e ξ ι C x0 L0) (localBase π e ξ ι C x0 L0) ι
        (root_compatible π e ξ ι C x0 L0) r))
  exact hi.trans hf

theorem outerMap_surjective (N : Subgroup D) [N.Normal] :
    Function.Surjective
      (TwistedSimpleRootCocycleCount.outerMap (localBase π e ξ ι C x0 L0) N) :=
  ActualComplementFullRootComponent.outerMap_surjective π x0
    (ActualWreathComplementFullRoot.component π ξ C.top_compatible x0) L0.val
    (ActualWreathComplementFullRoot.fullLocal_of_fullComponent π ξ C.top_compatible
      x0 L0.val L0.property) N

/-- The actual normal local image and its semisimple chart remain explicit.
Neither coordinatewise fullness nor a model name replaces the kernel chart. -/
theorem card_le_frame_outer_fibre [Finite Q] [Finite X] [Finite A] [Finite D]
    [MulAction.IsPretransitive Q X] [IsSimpleGroup A]
    (N : Subgroup D) [N.Normal] (hιN : ∀ a,ι a∈N)
    (CN : SemisimpleNormalChart N)
    (eN : quotientImage N (TwistedSimpleRootCocycleCount.zeroAxis (U := D)) ≃* A)
    (hZ : IsCenterless A) :
    (Nat.card (ActualWreathComplementFullRoot.FullFamily π ξ) : ℝ) ≤
      (Nat.card A : ℝ)^Nat.card X *
        (Nat.card (A ≃* A) *
          (Real.logb 2 (Nat.card
            (TwistedSimpleRootCocycleCount.outerMap (localBase π e ξ ι C x0 L0) N).ker) /
            Real.logb 2 (Nat.card A))) := by
  have hf : (Nat.card (ActualWreathComplementFullRoot.FullFamily π ξ) : ℝ) ≤
      (Nat.card A : ℝ)^Nat.card X * (Nat.card (FullRoot π e ξ ι C x0 L0) : ℝ) := by
    exact_mod_cast card_le_frame_root π e ξ ι C x0 L0
  have hr := TwistedSimpleRootCocycleCount.card_fullRoot_le
    (rootAction π e ξ ι C x0 L0) (localBase π e ξ ι C x0 L0) ι
    (root_compatible π e ξ ι C x0 L0) N hιN
    (outerMap_surjective π e ξ ι C x0 L0 N) CN eN hZ C.iota_injective
  exact hf.trans (mul_le_mul_of_nonneg_left hr (pow_nonneg (Nat.cast_nonneg _) _))

/-- A baseline is taken from the same full family; an empty family has
zero cardinality and requires no splitting choice. -/
theorem card_eq_zero_or_full_baseline :
    Nat.card (ActualWreathComplementFullRoot.FullFamily π ξ)=0 ∨
      Nonempty (ActualWreathComplementFullRoot.FullFamily π ξ) := by
  rcases ActualWreathComplementFullRoot.empty_or_full_component_baseline π ξ with h | h
  · letI := h
    exact Or.inl (Nat.card_of_isEmpty)
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.ActualWreathFullComplementFrameBound
