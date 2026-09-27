import SymmetricSubgroupAsymptotics.BinaryFourPairProfileUnion
import SymmetricSubgroupAsymptotics.BinaryResidualOrbitMenu

/-!
# The finite-menu four-pair Hall incidence

The complete bounded binary action menu is split into the original C2 and
E8 colours and the residual actions.  The common-label profile theorem then
has no supplied transitivity or action-separation assumptions.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryFourPairHallIncidence

abbrev ResidualProfile (N : ℕ) :=
  BinaryFourPairProfileUnion.Profile
    (α := BinaryResidualOrbitMenu.Label (2*N))

abbrev SourceFamily (N : ℕ) (S : Finset (ResidualProfile N)) :=
  BinaryFourPairProfileUnion.SourceSelected
    (BinaryResidualOrbitMenu.points (2*N))
    (BinaryResidualOrbitMenu.action (2*N)) (Fin (2*N)) S

abbrev TargetFamily (N : ℕ) (S : Finset (ResidualProfile N)) :=
  BinaryFourPairProfileUnion.TargetSelected
    (BinaryResidualOrbitMenu.points (2*N))
    (BinaryResidualOrbitMenu.action (2*N)) (Fin (2*N)) S

local instance sourceFamilyFinite (N : ℕ) (S : Finset (ResidualProfile N)) :
    Finite (SourceFamily N S) :=
  Finite.of_injective
    (fun H : SourceFamily N S => (H.val : Set (Equiv.Perm (Fin (2*N)))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance sourceFamilyFintype (N : ℕ) (S : Finset (ResidualProfile N)) :
    Fintype (SourceFamily N S) := Fintype.ofFinite _

local instance targetFamilyFinite (N : ℕ) (S : Finset (ResidualProfile N)) :
    Finite (TargetFamily N S) :=
  Finite.of_injective
    (fun H : TargetFamily N S => (H.val : Set (Equiv.Perm (Fin (2*N)))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

/-- The complete selected-profile numerical Hall theorem.  The only input
left is the finite selector itself and its exact degree equation. -/
theorem selected_frame_incidence (N : ℕ) (S : Finset (ResidualProfile N))
    (hsize : ∀ t ∈ S,
      BinaryFourPairProfileUnion.ProfileSize
        (BinaryResidualOrbitMenu.points (2*N)) N t) :
    (∑ H : SourceFamily N S,
      (Nat.card (PermutationPairOrbitCharacters.Frame H.val 4) : ℚ)) /
        (2*N).factorial ≤
      6*N * ((Nat.card (TargetFamily N S) : ℚ) / (2*N).factorial) :=
  BinaryFourPairProfileUnion.normalized_selected_frame_incidence
    (BinaryResidualOrbitMenu.points (2*N))
    (BinaryResidualOrbitMenu.action (2*N)) N S hsize
    (BinaryResidualOrbitMenu.action_transitive (2*N))
    (BinaryResidualOrbitMenu.e8_residual_separated (2*N))
    (BinaryResidualOrbitMenu.point_card_ne_two (2*N))

end SymmetricSubgroupAsymptotics.BinaryFourPairHallIncidence
