import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingCoherence

/-! The already constructed direction permutation sends entire axes
to entire axes, not merely individual edges. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
variable {I : Type*} {D : I → Type*}

def CoordinateAxis (i : I) (x : ∀ j, D j) : Set (∀ j, D j) :=
  {y | ∀ j, j ≠ i → x j = y j}

variable [DecidableEq I] [Finite I] [∀ i, Nontrivial (D i)]

theorem image_coordinateAxis (f : (∀ j, D j) ≃ (∀ j, D j))
    (hf : ∀ x y, ClosedAdjacent (f x) (f y) ↔ ClosedAdjacent x y)
    (base x : ∀ j, D j) (i : I) :
    f '' CoordinateAxis i x = CoordinateAxis (directionPermutation f hf base i) (f x) := by
  classical
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases he : x = y
    · subst y
      exact fun _ _ => rfl
    · have hxy : DirectionEdge i x y := by
        refine ⟨?_, hy⟩
        intro hi
        exact he (funext (fun j => by
          by_cases hj : j = i
          · subst j; exact hi
          · exact hy j hj))
      exact (image_edge_global_direction f hf base hxy).2
  · intro hz
    let y := f.symm z
    have hfy : f y = z := f.apply_symm_apply z
    have hxy : ClosedAdjacent x y := (hf x y).mp (by
      rw [hfy]
      exact closedAdjacent_of_axis (directionPermutation f hf base i) hz)
    rcases closedAdjacent_eq_or_edge hxy with he | ⟨j, hj⟩
    · refine ⟨y, ?_, hfy⟩
      intro k _
      exact congrFun he k
    · have hh := image_edge_global_direction f hf base hj
      rw [hfy] at hh
      have heq : directionPermutation f hf base j = directionPermutation f hf base i := by
        by_contra hne
        exact hh.1 (hz _ hne)
      have hji : j = i := (directionPermutation f hf base).injective heq
      refine ⟨y, ?_, hfy⟩
      intro k hk
      exact hj.2 k (by simpa only [hji] using hk)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
