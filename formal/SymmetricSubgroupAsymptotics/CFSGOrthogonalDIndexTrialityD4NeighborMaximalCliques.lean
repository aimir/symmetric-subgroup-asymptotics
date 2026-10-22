import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingMaximalCliques
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4CliqueFlags
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborTwins

/-! Maximal cliques in the ORIGINAL root-plane residue are literal
three-space tops or point stars in one of the two genuine maximal-space
components. Full neighbour fibres are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDIndexTrialityD4HammingTwins
variable (K : Type) [Field K]

def NeighborClique (S : Set (Neighbors K)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x = y ∨ NeighborAdjacent K x y

def MaximalNeighborClique (S : Set (Neighbors K)) : Prop :=
  NeighborClique K S ∧ ∀ T, NeighborClique K T → S ⊆ T → T ⊆ S

def neighborTop (W : ThreeExtensions K) : Set (Neighbors K) := {S | S.val ≤ W.val}
def neighborColumnStar (U : RootPoints K) (p : RulingParameters K) : Set (Neighbors K) :=
  {S | U.val ≤ S.val ∧ S.val ≤ (columnMaximalExtension K p).val}
def neighborRowStar (U : RootPoints K) (q : RulingParameters K) : Set (Neighbors K) :=
  {S | U.val ≤ S.val ∧ S.val ≤ (rowMaximalExtension K q).val}

theorem flag_firstAxis_eq_top (p q : RulingParameters K) :
    neighborFlagMap K ⁻¹' FirstAxis p q = neighborTop K (threeExtensionRulingEquiv K (p, q)) := by
  ext S
  change ((neighborOppositeParameters K S).1 = p ∧
    (neighborOppositeParameters K S).2 = q) ↔ _
  constructor
  · intro h
    exact (neighbor_parameters_eq_iff_top K S p q).mp (Prod.ext h.1 h.2)
  · intro h
    have he := (neighbor_parameters_eq_iff_top K S p q).mpr h
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem flag_secondAxis_eq_rowStar (U : RootPoints K) (q : RulingParameters K) :
    neighborFlagMap K ⁻¹' SecondAxis U q = neighborRowStar K U q := by
  ext S
  exact neighbor_point_row_iff_star K S U q

theorem flag_thirdAxis_eq_columnStar (U : RootPoints K) (p : RulingParameters K) :
    neighborFlagMap K ⁻¹' ThirdAxis U p = neighborColumnStar K U p := by
  ext S
  exact neighbor_point_column_iff_star K S U p

theorem maximal_neighbor_clique_geometric [Finite K] (S : Set (Neighbors K))
    (hS : MaximalNeighborClique K S) :
    (∃ W : ThreeExtensions K, S = neighborTop K W) ∨
      (∃ U : RootPoints K, ∃ p : RulingParameters K, S = neighborColumnStar K U p) ∨
      (∃ U : RootPoints K, ∃ q : RulingParameters K, S = neighborRowStar K U q) := by
  letI : Nontrivial (RootPoints K) := rootPoints_nontrivial K
  have hc := rulingParameter_card K
  letI : Finite (RulingParameters K) := Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  letI : Nontrivial (RulingParameters K) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hc]
    have hp : 0 < Nat.card K := Nat.card_pos
    omega)
  have hcl : ∀ T, NeighborClique K T ↔ PullbackClique (neighborFlagMap K) T := by
    intro T
    constructor
    · intro h x hx y hy
      exact (neighbor_closed_adj_iff K x y).mp (h x hx y hy)
    · intro h x hx y hy
      exact (neighbor_closed_adj_iff K x y).mpr (h x hx y hy)
  have hm : MaximalPullbackClique (neighborFlagMap K) S :=
    ⟨(hcl S).mp hS.1, fun T hT hST => hS.2 T ((hcl T).mpr hT) hST⟩
  obtain ⟨a, _, ha | ha | ha⟩ := maximal_pullback_eq_axis (neighborFlagMap K)
    (neighborFlagMap_surjective K) S hm
  · exact Or.inl ⟨threeExtensionRulingEquiv K (neighborOppositeParameters K a),
      ha.trans (flag_firstAxis_eq_top K _ _)⟩
  · exact Or.inr (Or.inr ⟨neighborPoint K a, (neighborOppositeParameters K a).2,
      ha.trans (flag_secondAxis_eq_rowStar K _ _)⟩)
  · exact Or.inr (Or.inl ⟨neighborPoint K a, (neighborOppositeParameters K a).1,
      ha.trans (flag_thirdAxis_eq_columnStar K _ _)⟩)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
