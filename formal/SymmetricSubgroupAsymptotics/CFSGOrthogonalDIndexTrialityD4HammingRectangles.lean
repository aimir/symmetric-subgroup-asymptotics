import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingDirection

/-! Literal coordinate rectangles make the local direction map of a
Hamming automorphism constant across each original edge. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
variable {I : Type*} [DecidableEq I] {D : I → Type*} [∀ i, Nontrivial (D i)]

def rectangleCorner (x y : ∀ i, D i) (j : I) : ∀ i, D i :=
  Function.update y j (otherValue x j)

theorem coordinate_rectangle {x y : ∀ i, D i} {i j : I}
    (hxy : DirectionEdge i x y) (hji : j ≠ i) :
    DirectionEdge j y (rectangleCorner x y j) ∧
    DirectionEdge i (coordinateStep x j) (rectangleCorner x y j) ∧
    ¬ClosedAdjacent y (coordinateStep x j) ∧ rectangleCorner x y j ≠ x := by
  have hij : i ≠ j := Ne.symm hji
  have hy : DirectionEdge j y (rectangleCorner x y j) := by
    constructor
    · change y j ≠ Function.update y j (otherValue x j) j
      rw [Function.update_self, ← hxy.2 j hji]
      exact Ne.symm (otherValue_ne x j)
    · intro k hkj
      exact (Function.update_of_ne hkj (otherValue x j) y).symm
  have hz : DirectionEdge i (coordinateStep x j) (rectangleCorner x y j) := by
    constructor
    · change Function.update x j (otherValue x j) i ≠ Function.update y j (otherValue x j) i
      simpa only [Function.update_of_ne hij] using hxy.1
    · intro k hki
      change Function.update x j (otherValue x j) k = Function.update y j (otherValue x j) k
      by_cases hkj : k = j
      · subst k
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
        exact hxy.2 k hki
  have hnot : ¬ClosedAdjacent y (coordinateStep x j) := by
    intro hc
    have hi : y i ≠ coordinateStep x j i := by
      simpa only [coordinateStep, Function.update_of_ne hij] using Ne.symm hxy.1
    have hj : y j ≠ coordinateStep x j j := by
      change y j ≠ Function.update x j (otherValue x j) j
      rw [Function.update_self, ← hxy.2 j hji]
      exact Ne.symm (otherValue_ne x j)
    exact hij (hc i j hi hj)
  have hne : rectangleCorner x y j ≠ x := by
    intro he
    have hh := congrArg (fun v => v i) he
    change Function.update y j (otherValue x j) i = x i at hh
    rw [Function.update_of_ne hij] at hh
    exact hxy.1 hh.symm
  exact ⟨hy, hz, hnot, hne⟩

variable (f : (∀ i, D i) ≃ (∀ i, D i))
  (hf : ∀ x y, ClosedAdjacent (f x) (f y) ↔ ClosedAdjacent x y)

theorem imageDirection_edge_constant {x y : ∀ i, D i} {i : I}
    (hxy : DirectionEdge i x y) : imageDirection f hf x = imageDirection f hf y := by
  funext j
  by_cases hji : j = i
  · subst j
    exact directionEdge_unique (image_edge_direction f hf hxy)
      (directionEdge_symm (image_edge_direction f hf (directionEdge_symm hxy)))
  · obtain ⟨hy, hz, hnot, hne⟩ := coordinate_rectangle hxy hji
    have hh := rectangle_opposite_directions
      (image_edge_direction f hf hxy) (image_edge_direction f hf (coordinateStep_edge x j))
      (image_edge_direction f hf hy) (image_edge_direction f hf hz)
      (fun h => hnot ((hf y (coordinateStep x j)).mp h))
      (fun h => hne (f.injective h))
    exact hh.1.symm

theorem imageDirection_axis_constant {x y : ∀ i, D i} (i : I)
    (hxy : ∀ j, j ≠ i → x j = y j) : imageDirection f hf x = imageDirection f hf y := by
  classical
  by_cases hi : x i = y i
  · have he : x = y := by
      funext j
      by_cases hji : j = i
      · subst j
        exact hi
      · exact hxy j hji
    exact congrArg (imageDirection f hf) he
  · exact imageDirection_edge_constant f hf ⟨hi, hxy⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
