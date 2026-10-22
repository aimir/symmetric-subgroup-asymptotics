import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborTwins

/-! The intrinsic true-twin quotient of the original D4 neighbour
graph is the full three-factor Hamming residue. Its equivalence is
proved from actual surjectivity and true-twin recognition, without a
building identification or global choice of triality direction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDIndexTrialityD4HammingTwins
variable (K : Type) [Field K] [Finite K]

def neighborTwinSetoid : Setoid (Neighbors K) where
  r := NeighborTrueTwins K
  iseqv := ⟨fun S => (neighbor_trueTwins_iff_flags K S S).mpr rfl,
    fun h => (neighbor_trueTwins_iff_flags K _ _).mpr
      ((neighbor_trueTwins_iff_flags K _ _).mp h).symm,
    fun h h' => (neighbor_trueTwins_iff_flags K _ _).mpr
      (((neighbor_trueTwins_iff_flags K _ _).mp h).trans
        ((neighbor_trueTwins_iff_flags K _ _).mp h'))⟩

abbrev NeighborTwinQuotient := Quotient (neighborTwinSetoid K)

def quotientFlags : NeighborTwinQuotient K →
    RootPoints K × (RulingParameters K × RulingParameters K) :=
  Quotient.lift (neighborFlagMap K)
    (fun S T h => (neighbor_trueTwins_iff_flags K S T).mp h)

theorem quotientFlags_injective : Function.Injective (quotientFlags K) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro S T he
  exact Quotient.sound ((neighbor_trueTwins_iff_flags K S T).mpr he)

theorem quotientFlags_surjective : Function.Surjective (quotientFlags K) := by
  intro p
  obtain ⟨S, hS⟩ := neighborFlagMap_surjective K p
  exact ⟨Quotient.mk (neighborTwinSetoid K) S, hS⟩

def neighborTwinQuotientEquiv : NeighborTwinQuotient K ≃
    RootPoints K × (RulingParameters K × RulingParameters K) :=
  Equiv.ofBijective (quotientFlags K) ⟨quotientFlags_injective K, quotientFlags_surjective K⟩

theorem neighborTwinQuotient_card :
    Nat.card (NeighborTwinQuotient K) = (Nat.card K + 1) ^ 3 := by
  rw [Nat.card_congr (neighborTwinQuotientEquiv K), Nat.card_prod, Nat.card_prod,
    rootPoints_card, rulingParameter_card]
  ring

def TwinQuotientAdjacent (x y : NeighborTwinQuotient K) : Prop :=
  x ≠ y ∧ TwoCoordinates (quotientFlags K x) (quotientFlags K y)

theorem twinQuotient_adjacent_iff (S T : Neighbors K) :
    TwinQuotientAdjacent K (Quotient.mk (neighborTwinSetoid K) S)
      (Quotient.mk (neighborTwinSetoid K) T) ↔
        ¬NeighborTrueTwins K S T ∧ NeighborAdjacent K S T := by
  change ((Quotient.mk (neighborTwinSetoid K) S ≠ Quotient.mk (neighborTwinSetoid K) T) ∧
    TwoCoordinates (neighborFlagMap K S) (neighborFlagMap K T)) ↔ _
  constructor
  · rintro ⟨hne, hc⟩
    have ht : ¬NeighborTrueTwins K S T := fun h => hne (Quotient.sound h)
    refine ⟨ht, ?_⟩
    rcases (neighbor_closed_adj_iff K S T).mpr hc with he | ha
    · exact False.elim (ht ((neighbor_trueTwins_iff_flags K S T).mpr (congrArg (neighborFlagMap K) he)))
    · exact ha
  · rintro ⟨ht, ha⟩
    exact ⟨fun he => ht (Quotient.exact he), (neighbor_closed_adj_iff K S T).mp (Or.inr ha)⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
