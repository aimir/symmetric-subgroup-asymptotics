import SymmetricSubgroupAsymptotics.MarkedC4ActualLargeOrbitRelativeRow
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! Roney--Dougal--Tracey, arXiv:2503.05416v1, Proposition 6.2,
p.21: for every rate>0, one cutoff makes the ordinary generator number of a
soluble permutation group at most rate times its degree, when its nontrivial
orbits exceed the cutoff. `PublishedProposition62` is this ordinary statement
on a finite point type. Relabelling the points does not change its content;
the trivial group and the empty point type contribute generator number zero.
The cutoff may be increased to 2.

Here the statement is applied to the range of the ACTUAL large-point
projection. Its orbits were already identified with the original orbits.
The resulting tuple is lifted to the SAME original source, retaining the
literal projection kernel. No container, recovery, or marked estimate is a
literature input in this file. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.LargeOrbitOrdinaryGeneration

open ActualLargeOrbitKernel ActualLargeOrbitImage

/-- The ordinary small-generator consequence of published Proposition 6.2.
Only ordinary soluble permutation groups occur in this hypothesis. -/
def PublishedProposition62 : Prop :=
  ∀ rate : ℝ, 0 < rate → ∃ C : ℕ, 2 ≤ C ∧
    ∀ (X : Type) [Fintype X] (H : Subgroup (Equiv.Perm X)) [IsSolvable H],
      (∀ x : X, 1 < Nat.card (MulAction.orbit H x) →
        C ≤ Nat.card (MulAction.orbit H x)) →
      (genRank H : ℝ) ≤ rate * Fintype.card X

/-- The fixed-length budget is independent of the source and of all marks. -/
def tupleLength (rate : ℝ) (b : ℕ) : ℕ := ⌈rate * b⌉₊

variable {C b : ℕ} {rate : ℝ}

theorem image_solvable (G : Subgroup (PermutationGroup b)) [IsSolvable G] :
    IsSolvable (projection G C).range :=
  solvable_of_surjective (f := (projection G C).rangeRestrict)
    (projection G C).rangeRestrict_surjective

/-- Bind the ordinary literature row to the exact projection and pad only
after taking its actual generating set. This also handles a trivial image. -/
theorem image_generators
    (hrate : 0 ≤ rate)
    (hordinary : ∀ (X : Type) [Fintype X]
      (H : Subgroup (Equiv.Perm X)) [IsSolvable H],
        (∀ x : X, 1 < Nat.card (MulAction.orbit H x) →
          C ≤ Nat.card (MulAction.orbit H x)) →
        (genRank H : ℝ) ≤ rate * Fintype.card X)
    (G : Subgroup (PermutationGroup b)) [IsSolvable G] :
    ∃ S : Finset (projection G C).range,
      S.card ≤ tupleLength rate b ∧
      Subgroup.closure (S : Set (projection G C).range) = ⊤ := by
  letI : Fintype (largePoints G C) := Fintype.ofFinite _
  letI : IsSolvable (projection G C).range := image_solvable G
  have hrank := hordinary (largePoints G C) (projection G C).range
    (fun x _ => orbit_lower G C x)
  have hdegree : Fintype.card (largePoints G C) ≤ b := by
    simpa only [Nat.card_eq_fintype_card] using degree_le G C
  have hdegree' : (Fintype.card (largePoints G C) : ℝ) ≤ b := by exact_mod_cast hdegree
  obtain ⟨S,hcard,hgen⟩ := genRank_spec (G := (projection G C).range)
  refine ⟨S,?_,hgen⟩
  have hbound : (S.card : ℝ) ≤ (tupleLength rate b : ℝ) := by
    rw [hcard]
    exact hrank.trans ((mul_le_mul_of_nonneg_left hdegree' hrate).trans (Nat.le_ceil _))
  exact_mod_cast hbound

/-- One cutoff gives relative tuples for every original degree and source.
The kernel and generators here are the literal objects used in recovery. -/
theorem exists_cutoff_relative_tuples (h62 : PublishedProposition62)
    (rate : ℝ) (hrate : 0 < rate) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ (b : ℕ) (G : Subgroup (PermutationGroup b)) [IsSolvable G],
        ∃ t : Fin (tupleLength rate b) → G,
          Subgroup.closure (Set.range t ∪ (projection G C).ker) = ⊤ := by
  obtain ⟨C,hC,hordinary⟩ := h62 rate hrate
  refine ⟨C,hC,?_⟩
  intro b G _
  exact ActualLargeOrbitRelative.exists_relative_tuple C G
    (image_generators hrate.le hordinary G)

end SymmetricSubgroupAsymptotics.MarkedC4.LargeOrbitOrdinaryGeneration
end
