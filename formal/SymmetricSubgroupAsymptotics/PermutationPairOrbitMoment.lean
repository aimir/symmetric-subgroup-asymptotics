import SymmetricSubgroupAsymptotics.PermutationPairOrbitCharacters
import SymmetricSubgroupAsymptotics.CharacterPairMomentBound

/-!
# The pair moment for an arbitrary original permutation-group family

The scalar character calculation is installed on actual two-point orbits.
Its collision marks are exactly the unordered physical duplicate marks.
The remaining input is the physical ordered-four incidence bound for the
chosen original family; no closure under a carrier fusion is assumed here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PermutationPairOrbitMoment

open PermutationPairOrbitMarks PermutationPairOrbitCharacters

variable {X : Type*} [Finite X]

local instance finiteSubgroups (G : Type*) [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

abbrev Family (P : Subgroup (Equiv.Perm X) → Prop) := {H // P H}

local instance familyFinite (P : Subgroup (Equiv.Perm X) → Prop) : Finite (Family P) :=
  Finite.of_injective (fun H : Family P => (H.val : Set (Equiv.Perm X)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance familyFintype (P : Subgroup (Equiv.Perm X) → Prop) : Fintype (Family P) :=
  @Fintype.ofFinite (Family P) (familyFinite P)

/-- No orientation or multiplicity is added when character collisions are
identified with the original unordered pair-orbit marks. -/
def collisionEquiv (H : Subgroup (Equiv.Perm X)) :
    CharacterCollisionCount.Collision (character H) ≃ DuplicateMark H :=
  Equiv.subtypeEquivRight (fun s => by
    constructor
    · rintro ⟨hc,he⟩
      exact ⟨hc,fun a ha b hb => (character_eq_iff H a b).mp (he a ha b hb)⟩
    · rintro ⟨hc,he⟩
      exact ⟨hc,fun a ha b hb => (character_eq_iff H a b).mpr (he a ha b hb)⟩)

theorem collision_card (H : Subgroup (Equiv.Perm X)) :
    Nat.card (CharacterCollisionCount.Collision (character H)) =
      Nat.card (DuplicateMark H) := Nat.card_congr (collisionEquiv H)

theorem frame_card (H : Subgroup (Equiv.Perm X)) (r : ℕ) :
    Nat.card (CharacterIndependentSelections.Frame (character H) r) =
      Nat.card (Frame H r) := rfl

/-- The physical incidence budget supplies the exact fourth-root moment
coefficient. The family predicate is arbitrary and the subgroups unchanged. -/
theorem pair_moment_of_four_incidence
    (P : Subgroup (Equiv.Perm X) → Prop) (A : ℝ) (hA : 0 ≤ A)
    (hinc : (∑ H : Family P, (Nat.card (Frame H.val 4) : ℝ)) ≤
      A * Nat.card (Family P)) :
    (∑ H : Family P, (Nat.card (PairOrbit H.val) : ℝ)) ≤
      (7 + A ^ (1 / 4 : ℝ)) * Nat.card (Family P) +
      ∑ H : Family P, (Nat.card (DuplicateMark H.val) : ℝ) := by
  have hc : Nat.card (Family P) = Fintype.card (Family P) := Nat.card_eq_fintype_card
  have h := CharacterPairMoment.aggregate_card_le_quarter_power
    (fun H : Family P => character H.val)
    (fun H => character_ne_zero H.val) A hA
    (by simpa only [frame_card, ← hc] using hinc)
  simpa only [collision_card, ← hc] using h

end SymmetricSubgroupAsymptotics.PermutationPairOrbitMoment
