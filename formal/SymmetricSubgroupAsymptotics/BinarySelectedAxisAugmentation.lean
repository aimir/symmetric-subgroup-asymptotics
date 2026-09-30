import SymmetricSubgroupAsymptotics.GeneratedSplitTopNormals.SelectedElementaryAxes
import SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitSplit

/-!
# Canonical augmentation modules for the selected degree-eight axes

The generated axis certificates exhibit the two actual orbit classes of each
surviving elementary index-two axis.  Consequently the two-orbit augmentation
module arising from the abstract filtration is independent of the order in
which those two classes were returned.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

open PermutationBinaryTwoOrbitSplit

/-- A side sum with its finite enumeration fixed internally. -/
def booleanSideSum {X : Type} [Finite X] (side : X → Bool) (b : Bool)
    (a : X → ZMod 2) : ZMod 2 :=
  letI : Fintype X := Fintype.ofFinite X
  ∑ x : {x : X // side x=b},a x

/-- The computable degree-eight version used by the finite catalogue checks. -/
def finEightBooleanSideSum (side : Fin 8 → Bool) (b : Bool)
    (a : Fin 8 → ZMod 2) : ZMod 2 :=
  ∑ x : {x : Fin 8 // side x=b},a x

private theorem sum_univ_independent {X A : Type} [AddCommMonoid A]
    (i j : Fintype X) (f : X → A) :
    @Finset.sum X A _ (@Finset.univ X i) f=
      @Finset.sum X A _ (@Finset.univ X j) f := by
  apply Finset.sum_congr
  · ext x
    simp
  · intro x _
    rfl

theorem booleanSideSum_eq_finEightBooleanSideSum
    (side : Fin 8 → Bool) (b : Bool) (a : Fin 8 → ZMod 2) :
    booleanSideSum side b a=finEightBooleanSideSum side b a := by
  unfold booleanSideSum finEightBooleanSideSum
  apply sum_univ_independent

/-- Replace an actual orbit subtype by any checked Boolean side carrying
exactly the same points. -/
def orbitBooleanSideEquiv {G X : Type} [Group G] [MulAction G X]
    (H : Subgroup G) (o : MulAction.orbitRel.Quotient H X)
    (side : X → Bool) (b : Bool)
    (hmem : ∀ x,x∈o.orbit ↔ side x=b) :
    o.orbit ≃ {x : X // side x=b} where
  toFun x := ⟨x,hmem x |>.mp x.property⟩
  invFun x := ⟨x,hmem x |>.mpr x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl

/-- Orbit sums can be evaluated on a checked Boolean side. -/
theorem orbitSum_eq_boolean_side {G X : Type} [Group G] [MulAction G X]
    [Finite X] (H : Subgroup G)
    (o : MulAction.orbitRel.Quotient H X)
    (side : X → Bool) (b : Bool)
    (hmem : ∀ x,x∈o.orbit ↔ side x=b) (a : X → ZMod 2) :
    orbitSum H o a=booleanSideSum side b a := by
  classical
  unfold booleanSideSum
  change (∑ x : o.orbit,a x)=∑ x : {x : X // side x=b},a x
  simpa using Equiv.sum_comp (orbitBooleanSideEquiv H o side b hmem)
    (fun x : {x : X // side x=b} => a x.val)

/-- Interchanging the two orbit equations does not change their joint kernel. -/
theorem twoOrbitAugmentation_comm {G X : Type} [Group G] [MulAction G X]
    [Finite X] (H : Subgroup G)
    (o₁ o₂ : MulAction.orbitRel.Quotient H X) :
    twoOrbitAugmentation H o₁ o₂=twoOrbitAugmentation H o₂ o₁ := by
  ext a
  change ((orbitSum H o₁ a,orbitSum H o₂ a)=(0,0)) ↔
    ((orbitSum H o₂ a,orbitSum H o₁ a)=(0,0))
  constructor
  · intro h
    apply Prod.ext
    · exact congrArg Prod.snd h
    · exact congrArg Prod.fst h
  · intro h
    apply Prod.ext
    · exact congrArg Prod.snd h
    · exact congrArg Prod.fst h

/-- When an action has exactly two displayed orbit classes, every ordered
pair of distinct orbit classes cuts out the displayed augmentation module. -/
theorem twoOrbitAugmentation_eq_of_two_classes {G X : Type}
    [Group G] [MulAction G X] [Finite X]
    (H : Subgroup G) (left right : MulAction.orbitRel.Quotient H X)
    (hcover : ∀ o : MulAction.orbitRel.Quotient H X,o=left ∨ o=right)
    (o₁ o₂ : MulAction.orbitRel.Quotient H X) (hne : o₁≠o₂) :
    twoOrbitAugmentation H o₁ o₂=twoOrbitAugmentation H left right := by
  rcases hcover o₁ with h₁ | h₁
  · rcases hcover o₂ with h₂ | h₂
    · exact (hne (h₁.trans h₂.symm)).elim
    · subst o₁
      subst o₂
      rfl
  · rcases hcover o₂ with h₂ | h₂
    · subst o₁
      subst o₂
      exact twoOrbitAugmentation_comm H right left
    · exact (hne (h₁.trans h₂.symm)).elim

namespace BinarySelectedAxis8T9

def selectedAugmentation : Submodule (ZMod 2) (Fin 8 → ZMod 2) :=
  twoOrbitAugmentation selectedAxis selectedLeftOrbit selectedRightOrbit

theorem mem_selectedAugmentation_iff (a : Fin 8 → ZMod 2) :
    a∈selectedAugmentation ↔
      (finEightBooleanSideSum selectedSide true a,
        finEightBooleanSideSum selectedSide false a)=(0,0) := by
  change (orbitSum selectedAxis selectedLeftOrbit a,
    orbitSum selectedAxis selectedRightOrbit a)=(0,0) ↔ _
  rw [orbitSum_eq_boolean_side selectedAxis selectedLeftOrbit selectedSide true
      mem_selectedLeftOrbit_iff,
    orbitSum_eq_boolean_side selectedAxis selectedRightOrbit selectedSide false
      mem_selectedRightOrbit_iff,
    booleanSideSum_eq_finEightBooleanSideSum,
    booleanSideSum_eq_finEightBooleanSideSum]

theorem augmentation_eq_selected
    (o₁ o₂ : MulAction.orbitRel.Quotient selectedAxis (Fin 8))
    (hne : o₁≠o₂) :
    twoOrbitAugmentation selectedAxis o₁ o₂=selectedAugmentation :=
  twoOrbitAugmentation_eq_of_two_classes selectedAxis
    selectedLeftOrbit selectedRightOrbit selected_orbits_cover o₁ o₂ hne

end BinarySelectedAxis8T9

namespace BinarySelectedAxis8T10

def selectedAugmentation : Submodule (ZMod 2) (Fin 8 → ZMod 2) :=
  twoOrbitAugmentation selectedAxis selectedLeftOrbit selectedRightOrbit

theorem mem_selectedAugmentation_iff (a : Fin 8 → ZMod 2) :
    a∈selectedAugmentation ↔
      (finEightBooleanSideSum selectedSide true a,
        finEightBooleanSideSum selectedSide false a)=(0,0) := by
  change (orbitSum selectedAxis selectedLeftOrbit a,
    orbitSum selectedAxis selectedRightOrbit a)=(0,0) ↔ _
  rw [orbitSum_eq_boolean_side selectedAxis selectedLeftOrbit selectedSide true
      mem_selectedLeftOrbit_iff,
    orbitSum_eq_boolean_side selectedAxis selectedRightOrbit selectedSide false
      mem_selectedRightOrbit_iff,
    booleanSideSum_eq_finEightBooleanSideSum,
    booleanSideSum_eq_finEightBooleanSideSum]

theorem augmentation_eq_selected
    (o₁ o₂ : MulAction.orbitRel.Quotient selectedAxis (Fin 8))
    (hne : o₁≠o₂) :
    twoOrbitAugmentation selectedAxis o₁ o₂=selectedAugmentation :=
  twoOrbitAugmentation_eq_of_two_classes selectedAxis
    selectedLeftOrbit selectedRightOrbit selected_orbits_cover o₁ o₂ hne

end BinarySelectedAxis8T10

namespace BinarySelectedAxis8T18

def selectedAugmentation : Submodule (ZMod 2) (Fin 8 → ZMod 2) :=
  twoOrbitAugmentation selectedAxis selectedLeftOrbit selectedRightOrbit

theorem mem_selectedAugmentation_iff (a : Fin 8 → ZMod 2) :
    a∈selectedAugmentation ↔
      (finEightBooleanSideSum selectedSide true a,
        finEightBooleanSideSum selectedSide false a)=(0,0) := by
  change (orbitSum selectedAxis selectedLeftOrbit a,
    orbitSum selectedAxis selectedRightOrbit a)=(0,0) ↔ _
  rw [orbitSum_eq_boolean_side selectedAxis selectedLeftOrbit selectedSide true
      mem_selectedLeftOrbit_iff,
    orbitSum_eq_boolean_side selectedAxis selectedRightOrbit selectedSide false
      mem_selectedRightOrbit_iff,
    booleanSideSum_eq_finEightBooleanSideSum,
    booleanSideSum_eq_finEightBooleanSideSum]

theorem augmentation_eq_selected
    (o₁ o₂ : MulAction.orbitRel.Quotient selectedAxis (Fin 8))
    (hne : o₁≠o₂) :
    twoOrbitAugmentation selectedAxis o₁ o₂=selectedAugmentation :=
  twoOrbitAugmentation_eq_of_two_classes selectedAxis
    selectedLeftOrbit selectedRightOrbit selected_orbits_cover o₁ o₂ hne

end BinarySelectedAxis8T18

end SymmetricSubgroupAsymptotics
