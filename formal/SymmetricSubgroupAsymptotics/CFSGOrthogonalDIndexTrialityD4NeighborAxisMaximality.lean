import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborMaximalCliques
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingAxisMaximality

/-! Each of the three actual geometric clique families is maximal in
the original neighbour residue. Together with the converse this is an
exact classification, still before the global coherence argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDIndexTrialityD4HammingTwins
variable (K : Type) [Field K] [Finite K]

private theorem neighbor_clique_pullback_iff (S : Set (Neighbors K)) :
    NeighborClique K S ↔ PullbackClique (neighborFlagMap K) S := by
  constructor
  · intro h x hx y hy
    exact (neighbor_closed_adj_iff K x y).mp (h x hx y hy)
  · intro h x hx y hy
    exact (neighbor_closed_adj_iff K x y).mpr (h x hx y hy)

private theorem neighbor_maximal_of_pullback (S : Set (Neighbors K))
    (h : MaximalPullbackClique (neighborFlagMap K) S) : MaximalNeighborClique K S :=
  ⟨(neighbor_clique_pullback_iff K S).mpr h.1,
    fun T hT hST => h.2 T ((neighbor_clique_pullback_iff K T).mp hT) hST⟩

private theorem ruling_nontrivial : Nontrivial (RulingParameters K) := by
  have hc := rulingParameter_card K
  letI : Finite (RulingParameters K) := Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  apply Finite.one_lt_card_iff_nontrivial.mp
  rw [hc]
  have hp : 0 < Nat.card K := Nat.card_pos
  omega

theorem neighborTop_maximal (W : ThreeExtensions K) :
    MaximalNeighborClique K (neighborTop K W) := by
  letI : Nontrivial (RootPoints K) := rootPoints_nontrivial K
  letI : Nontrivial (RulingParameters K) := ruling_nontrivial K
  obtain ⟨pq, rfl⟩ := (threeExtensionRulingEquiv K).surjective W
  have h := pullback_firstAxis_maximal (neighborFlagMap K) (neighborFlagMap_surjective K) pq.1 pq.2
  rw [flag_firstAxis_eq_top] at h
  exact neighbor_maximal_of_pullback K _ h

theorem neighborColumnStar_maximal (U : RootPoints K) (p : RulingParameters K) :
    MaximalNeighborClique K (neighborColumnStar K U p) := by
  letI : Nontrivial (RootPoints K) := rootPoints_nontrivial K
  letI : Nontrivial (RulingParameters K) := ruling_nontrivial K
  have h := pullback_thirdAxis_maximal (neighborFlagMap K) (neighborFlagMap_surjective K) U p
  rw [flag_thirdAxis_eq_columnStar] at h
  exact neighbor_maximal_of_pullback K _ h

theorem neighborRowStar_maximal (U : RootPoints K) (q : RulingParameters K) :
    MaximalNeighborClique K (neighborRowStar K U q) := by
  letI : Nontrivial (RootPoints K) := rootPoints_nontrivial K
  letI : Nontrivial (RulingParameters K) := ruling_nontrivial K
  have h := pullback_secondAxis_maximal (neighborFlagMap K) (neighborFlagMap_surjective K) U q
  rw [flag_secondAxis_eq_rowStar] at h
  exact neighbor_maximal_of_pullback K _ h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
