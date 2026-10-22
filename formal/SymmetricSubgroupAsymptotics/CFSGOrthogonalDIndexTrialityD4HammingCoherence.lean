import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingRectangles
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-! Coordinate-update connectivity makes the direction permutation
of an actual Hamming automorphism independent of the vertex. This
proves coherence inside the entire product residue; coherence between
different original D4 residues remains a separate geometric step. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
variable {I : Type*} [DecidableEq I] {D : I → Type*} [∀ i, Nontrivial (D i)]
variable (f : (∀ i, D i) ≃ (∀ i, D i))
  (hf : ∀ x y, ClosedAdjacent (f x) (f y) ↔ ClosedAdjacent x y)

theorem imageDirection_eq_of_finite_difference (S : Finset I) (x y : ∀ i, D i)
    (hxy : ∀ i, i ∉ S → x i = y i) : imageDirection f hf x = imageDirection f hf y := by
  classical
  induction S using Finset.induction_on generalizing x y with
  | empty =>
    have he : x = y := funext (fun i => hxy i (by simp))
    exact congrArg (imageDirection f hf) he
  | @insert i S hi ih =>
    let z : ∀ j, D j := Function.update x i (y i)
    have hxz : imageDirection f hf x = imageDirection f hf z := by
      apply imageDirection_axis_constant f hf i
      intro j hji
      exact (Function.update_of_ne hji (y i) x).symm
    have hzy : ∀ j, j ∉ S → z j = y j := by
      intro j hj
      by_cases hji : j = i
      · subst j
        exact Function.update_self i (y i) x
      · exact (Function.update_of_ne hji (y i) x).trans
          (hxy j (by simp only [Finset.mem_insert, not_or]; exact ⟨hji, hj⟩))
    exact hxz.trans (ih z y hzy)

theorem imageDirection_constant [Finite I] (x y : ∀ i, D i) :
    imageDirection f hf x = imageDirection f hf y := by
  letI : Fintype I := Fintype.ofFinite I
  exact imageDirection_eq_of_finite_difference f hf Finset.univ x y
    (fun i hi => False.elim (hi (Finset.mem_univ i)))

def directionPermutation [Finite I] (x : ∀ i, D i) : Equiv.Perm I :=
  Equiv.ofBijective (imageDirection f hf x)
    ⟨imageDirection_injective f hf x,
      Finite.surjective_of_injective (imageDirection_injective f hf x)⟩

theorem directionPermutation_independent [Finite I] (x y : ∀ i, D i) :
    directionPermutation f hf x = directionPermutation f hf y := by
  apply Equiv.ext
  exact congrFun (imageDirection_constant f hf x y)

theorem image_edge_global_direction [Finite I] (base : ∀ i, D i)
    {x y : ∀ i, D i} {i : I} (hxy : DirectionEdge i x y) :
    DirectionEdge (directionPermutation f hf base i) (f x) (f y) := by
  have hh := image_edge_direction f hf hxy
  have he := congrFun (imageDirection_constant f hf x base) i
  change DirectionEdge (imageDirection f hf base i) (f x) (f y)
  rw [← he]
  exact hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
