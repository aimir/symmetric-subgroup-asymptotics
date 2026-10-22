import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
import Mathlib.Logic.Equiv.Defs

/-! An actual Hamming-relation permutation sends each coordinate
line through an original vertex into one uniquely determined coordinate
line through its image. Distinct directions remain distinct. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
variable {I : Type*} {D : I → Type*} [∀ i, Nontrivial (D i)]

def otherValue (x : ∀ i, D i) (i : I) : D i := Classical.choose (exists_ne (x i))

theorem otherValue_ne (x : ∀ i, D i) (i : I) : otherValue x i ≠ x i :=
  Classical.choose_spec (exists_ne (x i))

variable [DecidableEq I]

def coordinateStep (x : ∀ i, D i) (i : I) : ∀ j, D j := Function.update x i (otherValue x i)

theorem coordinateStep_edge (x : ∀ i, D i) (i : I) : DirectionEdge i x (coordinateStep x i) := by
  constructor
  · simpa only [coordinateStep, Function.update_self] using Ne.symm (otherValue_ne x i)
  · intro j hji
    exact (Function.update_of_ne hji (otherValue x i) x).symm

variable (f : (∀ i, D i) ≃ (∀ i, D i))
  (hf : ∀ x y, ClosedAdjacent (f x) (f y) ↔ ClosedAdjacent x y)

include hf

theorem image_step_direction_exists (x : ∀ i, D i) (i : I) :
    ∃ k, DirectionEdge k (f x) (f (coordinateStep x i)) := by
  have hh := (hf x (coordinateStep x i)).mpr (directionEdge_closed (coordinateStep_edge x i))
  rcases closedAdjacent_eq_or_edge hh with he | he
  · exact False.elim ((coordinateStep_edge x i).1
      (congrArg (fun v => v i) (f.injective he)))
  · exact he

def imageDirection (x : ∀ i, D i) (i : I) : I := Classical.choose (image_step_direction_exists f hf x i)

theorem imageDirection_step_edge (x : ∀ i, D i) (i : I) :
    DirectionEdge (imageDirection f hf x i) (f x) (f (coordinateStep x i)) :=
  Classical.choose_spec (image_step_direction_exists f hf x i)

theorem image_axis_direction (x y : ∀ i, D i) (i : I)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    ∀ k, k ≠ imageDirection f hf x i → f y k = f x k := by
  apply common_neighbors_on_axis (imageDirection_step_edge f hf x i)
  · exact (hf y x).mpr (closedAdjacent_symm (closedAdjacent_of_axis i hxy))
  · apply (hf y (coordinateStep x i)).mpr
    apply closedAdjacent_of_axis i
    intro j hji
    exact (hxy j hji).symm.trans (Function.update_of_ne hji (otherValue x i) x).symm

theorem image_edge_direction {x y : ∀ i, D i} {i : I} (hxy : DirectionEdge i x y) :
    DirectionEdge (imageDirection f hf x i) (f x) (f y) := by
  have haxis := image_axis_direction f hf x y i hxy.2
  constructor
  · intro he
    have hall : f x = f y := by
      funext k
      by_cases hk : k = imageDirection f hf x i
      · subst k
        exact he
      · exact (haxis k hk).symm
    exact hxy.1 (congrArg (fun v => v i) (f.injective hall))
  · intro k hk
    exact (haxis k hk).symm

theorem imageDirection_injective (x : ∀ i, D i) : Function.Injective (imageDirection f hf x) := by
  intro i j hij
  by_contra hne
  have hi := imageDirection_step_edge f hf x i
  have hj := imageDirection_step_edge f hf x j
  have hclosed : ClosedAdjacent (f (coordinateStep x i)) (f (coordinateStep x j)) := by
    apply closedAdjacent_of_axis (imageDirection f hf x i)
    intro k hk
    exact (hi.2 k hk).symm.trans (hj.2 k (by simpa only [← hij] using hk))
  have hbefore := (hf (coordinateStep x i) (coordinateStep x j)).mp hclosed
  have hdi : coordinateStep x i i ≠ coordinateStep x j i := by
    simpa only [coordinateStep, Function.update_self, Function.update_of_ne hne] using otherValue_ne x i
  have hdj : coordinateStep x i j ≠ coordinateStep x j j := by
    simpa only [coordinateStep, Function.update_self, Function.update_of_ne (Ne.symm hne)]
      using Ne.symm (otherValue_ne x j)
  exact hne (hbefore i j hdi hdj)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
