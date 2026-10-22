import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborFibers
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootPoints
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins

/-! The true twins in the ORIGINAL D4 neighbour graph are precisely
the fibres of its three actual flag coordinates. The quotient relation
is therefore intrinsic; this still does not assert global coherence of
the three directions at different original root planes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDIndexTrialityD4HammingTwins
variable (K : Type) [Field K]

def neighborFlagMap (S : Neighbors K) :
    RootPoints K × (RulingParameters K × RulingParameters K) :=
  (neighborPoint K S, neighborOppositeParameters K S)

theorem neighborFlagMap_surjective [Finite K] : Function.Surjective (neighborFlagMap K) := by
  rintro ⟨U, pq⟩
  let W := threeExtensionRulingEquiv K pq
  have hp : 0 < Nat.card (NeighborFlagFiber K U W) := by
    rw [neighborFlagFiber_card]
    exact Nat.card_pos
  obtain ⟨S⟩ := (Nat.card_pos_iff.mp hp).1
  refine ⟨S.val, Prod.ext S.property.1 ?_⟩
  have hh := congrArg (fun M => (threeExtensionRulingEquiv K).symm M) S.property.2
  change neighborOppositeParameters K S.val = (threeExtensionRulingEquiv K).symm
    (threeExtensionRulingEquiv K pq) at hh
  exact hh.trans ((threeExtensionRulingEquiv K).symm_apply_apply pq)

theorem sameTwoNeighborFlags_iff_coordinates (S T : Neighbors K) :
    SameTwoNeighborFlags K S T ↔ TwoCoordinates (neighborFlagMap K S) (neighborFlagMap K T) := by
  constructor
  · rintro (⟨hU, hp | hq⟩ | hpq)
    · exact Or.inl ⟨hU, hp⟩
    · exact Or.inr (Or.inl ⟨hU, hq⟩)
    · exact Or.inr (Or.inr ⟨congrArg Prod.fst hpq, congrArg Prod.snd hpq⟩)
  · rintro (⟨hU, hp⟩ | ⟨hU, hq⟩ | ⟨hp, hq⟩)
    · exact Or.inl ⟨hU, Or.inl hp⟩
    · exact Or.inl ⟨hU, Or.inr hq⟩
    · exact Or.inr (Prod.ext hp hq)

theorem neighbor_closed_adj_iff (S T : Neighbors K) :
    (S = T ∨ NeighborAdjacent K S T) ↔
      TwoCoordinates (neighborFlagMap K S) (neighborFlagMap K T) := by
  constructor
  · rintro (rfl | h)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact (sameTwoNeighborFlags_iff_coordinates K S T).mp
        ((neighbor_adjacent_iff_two_flags K S T).mp h).2
  · intro h
    by_cases he : S = T
    · exact Or.inl he
    · exact Or.inr ((neighbor_adjacent_iff_two_flags K S T).mpr
        ⟨he, (sameTwoNeighborFlags_iff_coordinates K S T).mpr h⟩)

def NeighborTrueTwins (S T : Neighbors K) : Prop :=
  ∀ V, (S = V ∨ NeighborAdjacent K S V) ↔ (T = V ∨ NeighborAdjacent K T V)

theorem neighbor_trueTwins_iff_flags [Finite K] (S T : Neighbors K) :
    NeighborTrueTwins K S T ↔ neighborFlagMap K S = neighborFlagMap K T := by
  letI : Nontrivial (RootPoints K) := rootPoints_nontrivial K
  have hc := rulingParameter_card K
  letI : Finite (RulingParameters K) := Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  letI : Nontrivial (RulingParameters K) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hc]
    have hp : 0 < Nat.card K := Nat.card_pos
    omega)
  constructor
  · intro h
    apply (coordinate_fibres_eq_true_twins (neighborFlagMap K)
      (neighborFlagMap_surjective K) S T).mp
    intro V
    exact (neighbor_closed_adj_iff K S V).symm.trans
      ((h V).trans (neighbor_closed_adj_iff K T V))
  · intro h V
    rw [neighbor_closed_adj_iff, neighbor_closed_adj_iff, h]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
