import SymmetricSubgroupAsymptotics.FiniteSeedJoinEscapePropertyCoverage
import SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionEdgeProperty
import SymmetricSubgroupAsymptotics.PermutationPrimePowerSeedEscape
import SymmetricSubgroupAsymptotics.BinaryEightSeed8Transitivity
import SymmetricSubgroupAsymptotics.S8Seed8LowModels
import SymmetricSubgroupAsymptotics.S8Seed8LowRelations
import SymmetricSubgroupAsymptotics.S8Seed8LowJoinEscape
import SymmetricSubgroupAsymptotics.S8Seed8LowRoot97Canonical
import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.S8AboveSixteenBinarySeedCanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed8HighChunk0
import SymmetricSubgroupAsymptotics.S8Seed8HighChunk1
import SymmetricSubgroupAsymptotics.S8Seed8HighChunk2
import SymmetricSubgroupAsymptotics.S8Seed8HighChunk3
import SymmetricSubgroupAsymptotics.S8Seed8HighChunk4
import SymmetricSubgroupAsymptotics.S8Seed8HighChunk5
import SymmetricSubgroupAsymptotics.S8Seed8HighChunk6
import SymmetricSubgroupAsymptotics.S8Seed8HighChunk7

/-! Actual low-or-escape coverage above original8T8. Two literal low rows
are interchanged by the selected normalizer; their one incomparable join
contains an actual larger binary subgroup. Original points are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed8CanonicalCoverage
open S8Seed8LeftCosets S8Seed8LowModels

abbrev Escape (W : Subgroup Ambient) : Prop :=
  PermutationPrimePowerSeedEscape.ContainsAbove 2 16 W

def LowOrEscape (W : Subgroup Ambient) : Prop :=
  (∃ i : Fin 3, W = rows i) ∨ Escape W

theorem escape_of_extension (P W : Subgroup Ambient) (hPW : P ≤ W)
    (hP : IsPGroup 2 P) (hHP : H ≤ P) (hcard : 16 < Nat.card P) : Escape W :=
  ⟨P, hPW, hP,
    permutationSubgroupTransitive_mono H P hHP BinaryEightSeed8Transitivity.transitive,
    hcard⟩

theorem edge_low (j : Fin 3) (i : Fin 3) :
    ∃ k : Fin 3, MulAut.conj (S8Seed8NormalizerRoots.edgeConjugator j) • rows i = rows k := by
  fin_cases j
  · refine ⟨i, ?_⟩
    change MulAut.conj (1 : Ambient) • rows i = rows i
    simp only [map_one, one_smul]
  · refine ⟨i, ?_⟩
    change MulAut.conj (1 : Ambient) • rows i = rows i
    simp only [map_one, one_smul]
  · fin_cases i
    · refine ⟨0, ?_⟩
      change MulAut.conj S8Seed8NormalizerRoots.normalizer • rows 0 = rows 0
      rw [rows_zero]
      exact S8Seed8NormalizerRoots.normalizes_seed
    · exact ⟨2, S8Seed8LowRelations.normalizer_one⟩
    · exact ⟨1, S8Seed8LowRelations.normalizer_two⟩

theorem edge_property (j : Fin 3) (W : Subgroup Ambient) (hW : LowOrEscape W) :
    LowOrEscape (MulAut.conj (S8Seed8NormalizerRoots.edgeConjugator j) • W) := by
  rcases hW with ⟨i, rfl⟩ | hescape
  · obtain ⟨k, hk⟩ := edge_low j i
    exact Or.inl ⟨k, hk⟩
  · exact Or.inr (PermutationPrimePowerSeedEscape.conjugate 2 16 _ W hescape)

theorem root_property (k : Fin 102) : LowOrEscape
    (H ⊔ Subgroup.closure {representatives (S8Seed8NormalizerRoots.roots k)}) := by
  fin_cases k
  · exact Or.inl ⟨0,(root_closure 0).symm⟩
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 0)
      (S8Seed8HighChunk0.extended_isPGroup 0) le_sup_left (S8Seed8HighChunk0.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 1)
      (S8Seed8HighChunk0.extended_isPGroup 1) le_sup_left (S8Seed8HighChunk0.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 2)
      (S8Seed8HighChunk0.extended_isPGroup 2) le_sup_left (S8Seed8HighChunk0.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 3)
      (S8Seed8HighChunk0.extended_isPGroup 3) le_sup_left (S8Seed8HighChunk0.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 4)
      (S8Seed8HighChunk0.extended_isPGroup 4) le_sup_left (S8Seed8HighChunk0.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 5)
      (S8Seed8HighChunk0.extended_isPGroup 5) le_sup_left (S8Seed8HighChunk0.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 6)
      (S8Seed8HighChunk0.extended_isPGroup 6) le_sup_left (S8Seed8HighChunk0.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 7)
      (S8Seed8HighChunk0.extended_isPGroup 7) le_sup_left (S8Seed8HighChunk0.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 8)
      (S8Seed8HighChunk0.extended_isPGroup 8) le_sup_left (S8Seed8HighChunk0.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 9)
      (S8Seed8HighChunk0.extended_isPGroup 9) le_sup_left (S8Seed8HighChunk0.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 10)
      (S8Seed8HighChunk0.extended_isPGroup 10) le_sup_left (S8Seed8HighChunk0.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 11)
      (S8Seed8HighChunk0.extended_isPGroup 11) le_sup_left (S8Seed8HighChunk0.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk0.extended_le_adjoin 12)
      (S8Seed8HighChunk0.extended_isPGroup 12) le_sup_left (S8Seed8HighChunk0.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 0)
      (S8Seed8HighChunk1.extended_isPGroup 0) le_sup_left (S8Seed8HighChunk1.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 1)
      (S8Seed8HighChunk1.extended_isPGroup 1) le_sup_left (S8Seed8HighChunk1.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 2)
      (S8Seed8HighChunk1.extended_isPGroup 2) le_sup_left (S8Seed8HighChunk1.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 3)
      (S8Seed8HighChunk1.extended_isPGroup 3) le_sup_left (S8Seed8HighChunk1.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 4)
      (S8Seed8HighChunk1.extended_isPGroup 4) le_sup_left (S8Seed8HighChunk1.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 5)
      (S8Seed8HighChunk1.extended_isPGroup 5) le_sup_left (S8Seed8HighChunk1.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 6)
      (S8Seed8HighChunk1.extended_isPGroup 6) le_sup_left (S8Seed8HighChunk1.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 7)
      (S8Seed8HighChunk1.extended_isPGroup 7) le_sup_left (S8Seed8HighChunk1.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 8)
      (S8Seed8HighChunk1.extended_isPGroup 8) le_sup_left (S8Seed8HighChunk1.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 9)
      (S8Seed8HighChunk1.extended_isPGroup 9) le_sup_left (S8Seed8HighChunk1.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 10)
      (S8Seed8HighChunk1.extended_isPGroup 10) le_sup_left (S8Seed8HighChunk1.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 11)
      (S8Seed8HighChunk1.extended_isPGroup 11) le_sup_left (S8Seed8HighChunk1.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk1.extended_le_adjoin 12)
      (S8Seed8HighChunk1.extended_isPGroup 12) le_sup_left (S8Seed8HighChunk1.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 0)
      (S8Seed8HighChunk2.extended_isPGroup 0) le_sup_left (S8Seed8HighChunk2.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 1)
      (S8Seed8HighChunk2.extended_isPGroup 1) le_sup_left (S8Seed8HighChunk2.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 2)
      (S8Seed8HighChunk2.extended_isPGroup 2) le_sup_left (S8Seed8HighChunk2.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 3)
      (S8Seed8HighChunk2.extended_isPGroup 3) le_sup_left (S8Seed8HighChunk2.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 4)
      (S8Seed8HighChunk2.extended_isPGroup 4) le_sup_left (S8Seed8HighChunk2.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 5)
      (S8Seed8HighChunk2.extended_isPGroup 5) le_sup_left (S8Seed8HighChunk2.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 6)
      (S8Seed8HighChunk2.extended_isPGroup 6) le_sup_left (S8Seed8HighChunk2.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 7)
      (S8Seed8HighChunk2.extended_isPGroup 7) le_sup_left (S8Seed8HighChunk2.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 8)
      (S8Seed8HighChunk2.extended_isPGroup 8) le_sup_left (S8Seed8HighChunk2.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 9)
      (S8Seed8HighChunk2.extended_isPGroup 9) le_sup_left (S8Seed8HighChunk2.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 10)
      (S8Seed8HighChunk2.extended_isPGroup 10) le_sup_left (S8Seed8HighChunk2.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 11)
      (S8Seed8HighChunk2.extended_isPGroup 11) le_sup_left (S8Seed8HighChunk2.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk2.extended_le_adjoin 12)
      (S8Seed8HighChunk2.extended_isPGroup 12) le_sup_left (S8Seed8HighChunk2.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 0)
      (S8Seed8HighChunk3.extended_isPGroup 0) le_sup_left (S8Seed8HighChunk3.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 1)
      (S8Seed8HighChunk3.extended_isPGroup 1) le_sup_left (S8Seed8HighChunk3.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 2)
      (S8Seed8HighChunk3.extended_isPGroup 2) le_sup_left (S8Seed8HighChunk3.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 3)
      (S8Seed8HighChunk3.extended_isPGroup 3) le_sup_left (S8Seed8HighChunk3.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 4)
      (S8Seed8HighChunk3.extended_isPGroup 4) le_sup_left (S8Seed8HighChunk3.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 5)
      (S8Seed8HighChunk3.extended_isPGroup 5) le_sup_left (S8Seed8HighChunk3.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 6)
      (S8Seed8HighChunk3.extended_isPGroup 6) le_sup_left (S8Seed8HighChunk3.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 7)
      (S8Seed8HighChunk3.extended_isPGroup 7) le_sup_left (S8Seed8HighChunk3.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 8)
      (S8Seed8HighChunk3.extended_isPGroup 8) le_sup_left (S8Seed8HighChunk3.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 9)
      (S8Seed8HighChunk3.extended_isPGroup 9) le_sup_left (S8Seed8HighChunk3.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 10)
      (S8Seed8HighChunk3.extended_isPGroup 10) le_sup_left (S8Seed8HighChunk3.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 11)
      (S8Seed8HighChunk3.extended_isPGroup 11) le_sup_left (S8Seed8HighChunk3.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk3.extended_le_adjoin 12)
      (S8Seed8HighChunk3.extended_isPGroup 12) le_sup_left (S8Seed8HighChunk3.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 0)
      (S8Seed8HighChunk4.extended_isPGroup 0) le_sup_left (S8Seed8HighChunk4.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 1)
      (S8Seed8HighChunk4.extended_isPGroup 1) le_sup_left (S8Seed8HighChunk4.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 2)
      (S8Seed8HighChunk4.extended_isPGroup 2) le_sup_left (S8Seed8HighChunk4.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 3)
      (S8Seed8HighChunk4.extended_isPGroup 3) le_sup_left (S8Seed8HighChunk4.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 4)
      (S8Seed8HighChunk4.extended_isPGroup 4) le_sup_left (S8Seed8HighChunk4.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 5)
      (S8Seed8HighChunk4.extended_isPGroup 5) le_sup_left (S8Seed8HighChunk4.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 6)
      (S8Seed8HighChunk4.extended_isPGroup 6) le_sup_left (S8Seed8HighChunk4.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 7)
      (S8Seed8HighChunk4.extended_isPGroup 7) le_sup_left (S8Seed8HighChunk4.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 8)
      (S8Seed8HighChunk4.extended_isPGroup 8) le_sup_left (S8Seed8HighChunk4.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 9)
      (S8Seed8HighChunk4.extended_isPGroup 9) le_sup_left (S8Seed8HighChunk4.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 10)
      (S8Seed8HighChunk4.extended_isPGroup 10) le_sup_left (S8Seed8HighChunk4.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 11)
      (S8Seed8HighChunk4.extended_isPGroup 11) le_sup_left (S8Seed8HighChunk4.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk4.extended_le_adjoin 12)
      (S8Seed8HighChunk4.extended_isPGroup 12) le_sup_left (S8Seed8HighChunk4.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 0)
      (S8Seed8HighChunk5.extended_isPGroup 0) le_sup_left (S8Seed8HighChunk5.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 1)
      (S8Seed8HighChunk5.extended_isPGroup 1) le_sup_left (S8Seed8HighChunk5.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 2)
      (S8Seed8HighChunk5.extended_isPGroup 2) le_sup_left (S8Seed8HighChunk5.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 3)
      (S8Seed8HighChunk5.extended_isPGroup 3) le_sup_left (S8Seed8HighChunk5.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 4)
      (S8Seed8HighChunk5.extended_isPGroup 4) le_sup_left (S8Seed8HighChunk5.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 5)
      (S8Seed8HighChunk5.extended_isPGroup 5) le_sup_left (S8Seed8HighChunk5.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 6)
      (S8Seed8HighChunk5.extended_isPGroup 6) le_sup_left (S8Seed8HighChunk5.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 7)
      (S8Seed8HighChunk5.extended_isPGroup 7) le_sup_left (S8Seed8HighChunk5.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 8)
      (S8Seed8HighChunk5.extended_isPGroup 8) le_sup_left (S8Seed8HighChunk5.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 9)
      (S8Seed8HighChunk5.extended_isPGroup 9) le_sup_left (S8Seed8HighChunk5.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 10)
      (S8Seed8HighChunk5.extended_isPGroup 10) le_sup_left (S8Seed8HighChunk5.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 11)
      (S8Seed8HighChunk5.extended_isPGroup 11) le_sup_left (S8Seed8HighChunk5.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk5.extended_le_adjoin 12)
      (S8Seed8HighChunk5.extended_isPGroup 12) le_sup_left (S8Seed8HighChunk5.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 0)
      (S8Seed8HighChunk6.extended_isPGroup 0) le_sup_left (S8Seed8HighChunk6.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 1)
      (S8Seed8HighChunk6.extended_isPGroup 1) le_sup_left (S8Seed8HighChunk6.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 2)
      (S8Seed8HighChunk6.extended_isPGroup 2) le_sup_left (S8Seed8HighChunk6.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 3)
      (S8Seed8HighChunk6.extended_isPGroup 3) le_sup_left (S8Seed8HighChunk6.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 4)
      (S8Seed8HighChunk6.extended_isPGroup 4) le_sup_left (S8Seed8HighChunk6.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 5)
      (S8Seed8HighChunk6.extended_isPGroup 5) le_sup_left (S8Seed8HighChunk6.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 6)
      (S8Seed8HighChunk6.extended_isPGroup 6) le_sup_left (S8Seed8HighChunk6.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 7)
      (S8Seed8HighChunk6.extended_isPGroup 7) le_sup_left (S8Seed8HighChunk6.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 8)
      (S8Seed8HighChunk6.extended_isPGroup 8) le_sup_left (S8Seed8HighChunk6.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 9)
      (S8Seed8HighChunk6.extended_isPGroup 9) le_sup_left (S8Seed8HighChunk6.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 10)
      (S8Seed8HighChunk6.extended_isPGroup 10) le_sup_left (S8Seed8HighChunk6.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 11)
      (S8Seed8HighChunk6.extended_isPGroup 11) le_sup_left (S8Seed8HighChunk6.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk6.extended_le_adjoin 12)
      (S8Seed8HighChunk6.extended_isPGroup 12) le_sup_left (S8Seed8HighChunk6.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk7.extended_le_adjoin 0)
      (S8Seed8HighChunk7.extended_isPGroup 0) le_sup_left (S8Seed8HighChunk7.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk7.extended_le_adjoin 1)
      (S8Seed8HighChunk7.extended_isPGroup 1) le_sup_left (S8Seed8HighChunk7.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk7.extended_le_adjoin 2)
      (S8Seed8HighChunk7.extended_isPGroup 2) le_sup_left (S8Seed8HighChunk7.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk7.extended_le_adjoin 3)
      (S8Seed8HighChunk7.extended_isPGroup 3) le_sup_left (S8Seed8HighChunk7.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk7.extended_le_adjoin 4)
      (S8Seed8HighChunk7.extended_isPGroup 4) le_sup_left (S8Seed8HighChunk7.extended_card_gt 4))
  · exact Or.inl ⟨1,(root_closure 97).symm⟩
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk7.extended_le_adjoin 5)
      (S8Seed8HighChunk7.extended_isPGroup 5) le_sup_left (S8Seed8HighChunk7.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk7.extended_le_adjoin 6)
      (S8Seed8HighChunk7.extended_isPGroup 6) le_sup_left (S8Seed8HighChunk7.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk7.extended_le_adjoin 7)
      (S8Seed8HighChunk7.extended_isPGroup 7) le_sup_left (S8Seed8HighChunk7.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed8HighChunk7.extended_le_adjoin 8)
      (S8Seed8HighChunk7.extended_isPGroup 8) le_sup_left (S8Seed8HighChunk7.extended_card_gt 8))

theorem adjoin_property (g : Ambient) : LowOrEscape (H ⊔ Subgroup.closure {g}) := by
  obtain ⟨i, hi⟩ := S8Seed8LeftCosets.covers g
  have he := FiniteLeftCosetCover.adjoin_eq_of_same_left_coset
    (H := H) g (representatives i) hi
  have hp := S8Seed8NormalizerRoots.reduction.edge_property_representative
    LowOrEscape (by
      intro a ha W hW
      change LowOrEscape (MulAut.conj
        (S8Seed8NormalizerRoots.edgeConjugator (S8Seed8NormalizerRoots.letters a)) • W)
      exact edge_property _ W hW) root_property i
  rw [← he] at hp
  exact hp

theorem low_join_escape : Escape (rows 1 ⊔ rows 2) :=
  escape_of_extension _ _ S8Seed8LowJoinEscape.extended_le_join
    S8Seed8LowJoinEscape.extended_isPGroup le_sup_left
    S8Seed8LowJoinEscape.extended_card_gt

theorem join_property (i j : Fin 3) : LowOrEscape (rows i ⊔ rows j) := by
  fin_cases i <;> fin_cases j
  · exact Or.inl ⟨0, sup_idem _⟩
  · exact Or.inl ⟨1, sup_eq_right.mpr (by change rows 0 ≤ rows 1; rw [rows_zero]; exact seed_le 1)⟩
  · exact Or.inl ⟨2, sup_eq_right.mpr (by change rows 0 ≤ rows 2; rw [rows_zero]; exact seed_le 2)⟩
  · exact Or.inl ⟨1, sup_eq_left.mpr (by change rows 0 ≤ rows 1; rw [rows_zero]; exact seed_le 1)⟩
  · exact Or.inl ⟨1, sup_idem _⟩
  · exact Or.inr low_join_escape
  · exact Or.inl ⟨2, sup_eq_left.mpr (by change rows 0 ≤ rows 2; rw [rows_zero]; exact seed_le 2)⟩
  · rw [sup_comm]
    exact Or.inr low_join_escape
  · exact Or.inl ⟨2, sup_idem _⟩

theorem complete (U : Subgroup Ambient) (hHU : H ≤ U) : LowOrEscape U :=
  FiniteSeedJoinEscapePropertyCoverage.complete_above H Escape
    (fun V W hVW hV => PermutationPrimePowerSeedEscape.mono 2 16 V W hVW hV)
    rows seed_le ⟨0, rows_zero⟩ adjoin_property join_property U hHU

theorem low_or_escape_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) :
    (∃ i : Fin 3, ∃ d : Ambient, MulAut.conj d • U = rows i) ∨ Escape U := by
  have hHU : H ≤ MulAut.conj c • U := by
    rw [← hc]
    change Q.map (MulAut.conj c).toMonoidHom ≤ U.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hQU
  rcases complete (MulAut.conj c • U) hHU with ⟨i, hi⟩ | hescape
  · exact Or.inl ⟨i, c, hi⟩
  · right
    have h := PermutationPrimePowerSeedEscape.conjugate 2 16 c⁻¹ _ hescape
    simpa only [map_inv, inv_smul_smul] using h

theorem seed_isPGroup : IsPGroup 2 H :=
  IsPGroup.of_card (n := 4) BinaryMenuCayley8T8.exact_card

theorem low_one_canonical :
    MulAut.conj S8Seed8LowRoot97Canonical.conjugator • rows 1 =
      PrimitiveAffineEightTop14CatalogueBinding.catalogueAction := by
  change MulAut.conj S8Seed8LowRoot97Canonical.conjugator • S8Seed8LowRoot97Canonical.lowRow = _
  exact S8Seed8LowRoot97Canonical.canonical_conjugated

theorem low_two_canonical :
    MulAut.conj (S8Seed8LowRoot97Canonical.conjugator*S8Seed8NormalizerRoots.normalizer⁻¹) • rows 2 =
      PrimitiveAffineEightTop14CatalogueBinding.catalogueAction := by
  rw [map_mul,mul_smul,S8Seed8LowRelations.inverse_normalizer_two]
  exact low_one_canonical

private theorem low_canonical (U : Subgroup Ambient) (hnot : ¬IsPGroup 2 U)
    (i : Fin 3) (d : Ambient) (hd : MulAut.conj d • U = rows i) :
    ∃ j : Fin 24,∃ c : Ambient,
      MulAut.conj c • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical j := by
  fin_cases i
  · have hc : MulAut.conj d • U = H := hd.trans rows_zero
    exact (hnot (S8CanonicalNonbinaryTransport.isPGroup_of_conjugate U H d hc seed_isPGroup)).elim
  · refine ⟨13,S8Seed8LowRoot97Canonical.conjugator*d,?_⟩
    rw [map_mul,mul_smul,hd]
    exact low_one_canonical
  · refine ⟨13,(S8Seed8LowRoot97Canonical.conjugator*S8Seed8NormalizerRoots.normalizer⁻¹)*d,?_⟩
    rw [map_mul,mul_smul,hd]
    exact low_two_canonical

theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬IsPGroup 2 U) :
    ∃ i : Fin 24,∃ d : Ambient,
      MulAut.conj d • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  rcases low_or_escape_of_conjugate U Q hQU c hc with ⟨i,d,hd⟩ | ⟨P,hPU,hp,ht,hcard⟩
  · exact low_canonical U hnot i d hd
  · exact S8AboveSixteenBinarySeedCanonicalCoverage.complete U P hPU hp ht hcard hnot

end SymmetricSubgroupAsymptotics.S8Seed8CanonicalCoverage
end
