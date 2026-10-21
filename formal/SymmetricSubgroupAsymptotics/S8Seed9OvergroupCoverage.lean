import SymmetricSubgroupAsymptotics.FiniteSeedJoinEscapePropertyCoverage
import SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionEdgeProperty
import SymmetricSubgroupAsymptotics.PermutationPrimePowerSeedEscape
import SymmetricSubgroupAsymptotics.BinaryEightSeed9Transitivity
import SymmetricSubgroupAsymptotics.S8Seed9LowModels
import SymmetricSubgroupAsymptotics.S8Seed9LowRelations
import SymmetricSubgroupAsymptotics.S8Seed9LowJoin1_2
import SymmetricSubgroupAsymptotics.S8Seed9LowJoin1_3
import SymmetricSubgroupAsymptotics.S8Seed9LowJoin1_4
import SymmetricSubgroupAsymptotics.S8Seed9LowJoin2_4
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk0
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk1
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk2
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk3
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk4
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk5
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk6
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk7
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk8
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk9
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk10
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk11
import SymmetricSubgroupAsymptotics.S8Seed9HighChunk12

/-! Actual low-or-escape coverage above original8T9. Four literal low rows
are interchanged in pairs by the selected normalizer. Every incomparable
join contains an actual larger binary subgroup. Original points retained. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed9OvergroupCoverage
open S8Seed9LeftCosets S8Seed9LowModels

abbrev Escape (W : Subgroup Ambient) : Prop :=
  PermutationPrimePowerSeedEscape.ContainsAbove 2 16 W

def LowOrEscape (W : Subgroup Ambient) : Prop :=
  (∃ i : Fin 5, W = rows i) ∨ Escape W

theorem escape_of_extension (P W : Subgroup Ambient) (hPW : P ≤ W)
    (hP : IsPGroup 2 P) (hHP : H ≤ P) (hcard : 16 < Nat.card P) : Escape W :=
  ⟨P, hPW, hP,
    permutationSubgroupTransitive_mono H P hHP BinaryEightSeed9Transitivity.transitive,
    hcard⟩

theorem edge_low (j : Fin 5) (i : Fin 5) :
    ∃ k : Fin 5, MulAut.conj (S8Seed9NormalizerRoots.edgeConjugator j) • rows i = rows k := by
  fin_cases j
  · refine ⟨i, ?_⟩
    change MulAut.conj (1 : Ambient) • rows i = rows i
    simp only [map_one, one_smul]
  · refine ⟨i, ?_⟩
    change MulAut.conj (1 : Ambient) • rows i = rows i
    simp only [map_one, one_smul]
  · refine ⟨i, ?_⟩
    change MulAut.conj (1 : Ambient) • rows i = rows i
    simp only [map_one, one_smul]
  · refine ⟨i, ?_⟩
    change MulAut.conj (1 : Ambient) • rows i = rows i
    simp only [map_one, one_smul]
  · fin_cases i
    · refine ⟨0, ?_⟩
      change MulAut.conj S8Seed9NormalizerRoots.normalizer • rows 0 = rows 0
      rw [rows_zero]
      exact S8Seed9NormalizerRoots.normalizes_seed
    · exact ⟨3, S8Seed9LowRelations.normalizer_one⟩
    · exact ⟨4, S8Seed9LowRelations.normalizer_two⟩
    · exact ⟨1, S8Seed9LowRelations.normalizer_three⟩
    · exact ⟨2, S8Seed9LowRelations.normalizer_four⟩

theorem edge_property (j : Fin 5) (W : Subgroup Ambient) (hW : LowOrEscape W) :
    LowOrEscape (MulAut.conj (S8Seed9NormalizerRoots.edgeConjugator j) • W) := by
  rcases hW with ⟨i, rfl⟩ | hescape
  · obtain ⟨k, hk⟩ := edge_low j i
    exact Or.inl ⟨k, hk⟩
  · exact Or.inr (PermutationPrimePowerSeedEscape.conjugate 2 16 _ W hescape)

theorem root_property (k : Fin 164) : LowOrEscape
    (H ⊔ Subgroup.closure {representatives (S8Seed9NormalizerRoots.roots k)}) := by
  fin_cases k
  · exact Or.inl ⟨0,(root_closure 0).symm⟩
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 0)
      (S8Seed9HighChunk0.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk0.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 1)
      (S8Seed9HighChunk0.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk0.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 2)
      (S8Seed9HighChunk0.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk0.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 3)
      (S8Seed9HighChunk0.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk0.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 4)
      (S8Seed9HighChunk0.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk0.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 5)
      (S8Seed9HighChunk0.extended_isPGroup 5) le_sup_left (S8Seed9HighChunk0.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 6)
      (S8Seed9HighChunk0.extended_isPGroup 6) le_sup_left (S8Seed9HighChunk0.extended_card_gt 6))
  · exact Or.inl ⟨1,(root_closure 8).symm⟩
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 7)
      (S8Seed9HighChunk0.extended_isPGroup 7) le_sup_left (S8Seed9HighChunk0.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 8)
      (S8Seed9HighChunk0.extended_isPGroup 8) le_sup_left (S8Seed9HighChunk0.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 9)
      (S8Seed9HighChunk0.extended_isPGroup 9) le_sup_left (S8Seed9HighChunk0.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 10)
      (S8Seed9HighChunk0.extended_isPGroup 10) le_sup_left (S8Seed9HighChunk0.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 11)
      (S8Seed9HighChunk0.extended_isPGroup 11) le_sup_left (S8Seed9HighChunk0.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk0.extended_le_adjoin 12)
      (S8Seed9HighChunk0.extended_isPGroup 12) le_sup_left (S8Seed9HighChunk0.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 0)
      (S8Seed9HighChunk1.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk1.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 1)
      (S8Seed9HighChunk1.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk1.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 2)
      (S8Seed9HighChunk1.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk1.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 3)
      (S8Seed9HighChunk1.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk1.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 4)
      (S8Seed9HighChunk1.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk1.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 5)
      (S8Seed9HighChunk1.extended_isPGroup 5) le_sup_left (S8Seed9HighChunk1.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 6)
      (S8Seed9HighChunk1.extended_isPGroup 6) le_sup_left (S8Seed9HighChunk1.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 7)
      (S8Seed9HighChunk1.extended_isPGroup 7) le_sup_left (S8Seed9HighChunk1.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 8)
      (S8Seed9HighChunk1.extended_isPGroup 8) le_sup_left (S8Seed9HighChunk1.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 9)
      (S8Seed9HighChunk1.extended_isPGroup 9) le_sup_left (S8Seed9HighChunk1.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 10)
      (S8Seed9HighChunk1.extended_isPGroup 10) le_sup_left (S8Seed9HighChunk1.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 11)
      (S8Seed9HighChunk1.extended_isPGroup 11) le_sup_left (S8Seed9HighChunk1.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk1.extended_le_adjoin 12)
      (S8Seed9HighChunk1.extended_isPGroup 12) le_sup_left (S8Seed9HighChunk1.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 0)
      (S8Seed9HighChunk2.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk2.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 1)
      (S8Seed9HighChunk2.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk2.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 2)
      (S8Seed9HighChunk2.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk2.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 3)
      (S8Seed9HighChunk2.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk2.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 4)
      (S8Seed9HighChunk2.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk2.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 5)
      (S8Seed9HighChunk2.extended_isPGroup 5) le_sup_left (S8Seed9HighChunk2.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 6)
      (S8Seed9HighChunk2.extended_isPGroup 6) le_sup_left (S8Seed9HighChunk2.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 7)
      (S8Seed9HighChunk2.extended_isPGroup 7) le_sup_left (S8Seed9HighChunk2.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 8)
      (S8Seed9HighChunk2.extended_isPGroup 8) le_sup_left (S8Seed9HighChunk2.extended_card_gt 8))
  · exact Or.inl ⟨2,(root_closure 37).symm⟩
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 9)
      (S8Seed9HighChunk2.extended_isPGroup 9) le_sup_left (S8Seed9HighChunk2.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 10)
      (S8Seed9HighChunk2.extended_isPGroup 10) le_sup_left (S8Seed9HighChunk2.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 11)
      (S8Seed9HighChunk2.extended_isPGroup 11) le_sup_left (S8Seed9HighChunk2.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk2.extended_le_adjoin 12)
      (S8Seed9HighChunk2.extended_isPGroup 12) le_sup_left (S8Seed9HighChunk2.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 0)
      (S8Seed9HighChunk3.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk3.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 1)
      (S8Seed9HighChunk3.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk3.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 2)
      (S8Seed9HighChunk3.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk3.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 3)
      (S8Seed9HighChunk3.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk3.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 4)
      (S8Seed9HighChunk3.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk3.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 5)
      (S8Seed9HighChunk3.extended_isPGroup 5) le_sup_left (S8Seed9HighChunk3.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 6)
      (S8Seed9HighChunk3.extended_isPGroup 6) le_sup_left (S8Seed9HighChunk3.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 7)
      (S8Seed9HighChunk3.extended_isPGroup 7) le_sup_left (S8Seed9HighChunk3.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 8)
      (S8Seed9HighChunk3.extended_isPGroup 8) le_sup_left (S8Seed9HighChunk3.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 9)
      (S8Seed9HighChunk3.extended_isPGroup 9) le_sup_left (S8Seed9HighChunk3.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 10)
      (S8Seed9HighChunk3.extended_isPGroup 10) le_sup_left (S8Seed9HighChunk3.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 11)
      (S8Seed9HighChunk3.extended_isPGroup 11) le_sup_left (S8Seed9HighChunk3.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk3.extended_le_adjoin 12)
      (S8Seed9HighChunk3.extended_isPGroup 12) le_sup_left (S8Seed9HighChunk3.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 0)
      (S8Seed9HighChunk4.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk4.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 1)
      (S8Seed9HighChunk4.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk4.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 2)
      (S8Seed9HighChunk4.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk4.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 3)
      (S8Seed9HighChunk4.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk4.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 4)
      (S8Seed9HighChunk4.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk4.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 5)
      (S8Seed9HighChunk4.extended_isPGroup 5) le_sup_left (S8Seed9HighChunk4.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 6)
      (S8Seed9HighChunk4.extended_isPGroup 6) le_sup_left (S8Seed9HighChunk4.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 7)
      (S8Seed9HighChunk4.extended_isPGroup 7) le_sup_left (S8Seed9HighChunk4.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 8)
      (S8Seed9HighChunk4.extended_isPGroup 8) le_sup_left (S8Seed9HighChunk4.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 9)
      (S8Seed9HighChunk4.extended_isPGroup 9) le_sup_left (S8Seed9HighChunk4.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 10)
      (S8Seed9HighChunk4.extended_isPGroup 10) le_sup_left (S8Seed9HighChunk4.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 11)
      (S8Seed9HighChunk4.extended_isPGroup 11) le_sup_left (S8Seed9HighChunk4.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk4.extended_le_adjoin 12)
      (S8Seed9HighChunk4.extended_isPGroup 12) le_sup_left (S8Seed9HighChunk4.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 0)
      (S8Seed9HighChunk5.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk5.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 1)
      (S8Seed9HighChunk5.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk5.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 2)
      (S8Seed9HighChunk5.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk5.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 3)
      (S8Seed9HighChunk5.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk5.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 4)
      (S8Seed9HighChunk5.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk5.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 5)
      (S8Seed9HighChunk5.extended_isPGroup 5) le_sup_left (S8Seed9HighChunk5.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 6)
      (S8Seed9HighChunk5.extended_isPGroup 6) le_sup_left (S8Seed9HighChunk5.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 7)
      (S8Seed9HighChunk5.extended_isPGroup 7) le_sup_left (S8Seed9HighChunk5.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 8)
      (S8Seed9HighChunk5.extended_isPGroup 8) le_sup_left (S8Seed9HighChunk5.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 9)
      (S8Seed9HighChunk5.extended_isPGroup 9) le_sup_left (S8Seed9HighChunk5.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 10)
      (S8Seed9HighChunk5.extended_isPGroup 10) le_sup_left (S8Seed9HighChunk5.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 11)
      (S8Seed9HighChunk5.extended_isPGroup 11) le_sup_left (S8Seed9HighChunk5.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk5.extended_le_adjoin 12)
      (S8Seed9HighChunk5.extended_isPGroup 12) le_sup_left (S8Seed9HighChunk5.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 0)
      (S8Seed9HighChunk6.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk6.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 1)
      (S8Seed9HighChunk6.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk6.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 2)
      (S8Seed9HighChunk6.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk6.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 3)
      (S8Seed9HighChunk6.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk6.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 4)
      (S8Seed9HighChunk6.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk6.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 5)
      (S8Seed9HighChunk6.extended_isPGroup 5) le_sup_left (S8Seed9HighChunk6.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 6)
      (S8Seed9HighChunk6.extended_isPGroup 6) le_sup_left (S8Seed9HighChunk6.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 7)
      (S8Seed9HighChunk6.extended_isPGroup 7) le_sup_left (S8Seed9HighChunk6.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 8)
      (S8Seed9HighChunk6.extended_isPGroup 8) le_sup_left (S8Seed9HighChunk6.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 9)
      (S8Seed9HighChunk6.extended_isPGroup 9) le_sup_left (S8Seed9HighChunk6.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 10)
      (S8Seed9HighChunk6.extended_isPGroup 10) le_sup_left (S8Seed9HighChunk6.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 11)
      (S8Seed9HighChunk6.extended_isPGroup 11) le_sup_left (S8Seed9HighChunk6.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk6.extended_le_adjoin 12)
      (S8Seed9HighChunk6.extended_isPGroup 12) le_sup_left (S8Seed9HighChunk6.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 0)
      (S8Seed9HighChunk7.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk7.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 1)
      (S8Seed9HighChunk7.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk7.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 2)
      (S8Seed9HighChunk7.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk7.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 3)
      (S8Seed9HighChunk7.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk7.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 4)
      (S8Seed9HighChunk7.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk7.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 5)
      (S8Seed9HighChunk7.extended_isPGroup 5) le_sup_left (S8Seed9HighChunk7.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 6)
      (S8Seed9HighChunk7.extended_isPGroup 6) le_sup_left (S8Seed9HighChunk7.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 7)
      (S8Seed9HighChunk7.extended_isPGroup 7) le_sup_left (S8Seed9HighChunk7.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 8)
      (S8Seed9HighChunk7.extended_isPGroup 8) le_sup_left (S8Seed9HighChunk7.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 9)
      (S8Seed9HighChunk7.extended_isPGroup 9) le_sup_left (S8Seed9HighChunk7.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 10)
      (S8Seed9HighChunk7.extended_isPGroup 10) le_sup_left (S8Seed9HighChunk7.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 11)
      (S8Seed9HighChunk7.extended_isPGroup 11) le_sup_left (S8Seed9HighChunk7.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk7.extended_le_adjoin 12)
      (S8Seed9HighChunk7.extended_isPGroup 12) le_sup_left (S8Seed9HighChunk7.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 0)
      (S8Seed9HighChunk8.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk8.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 1)
      (S8Seed9HighChunk8.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk8.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 2)
      (S8Seed9HighChunk8.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk8.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 3)
      (S8Seed9HighChunk8.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk8.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 4)
      (S8Seed9HighChunk8.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk8.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 5)
      (S8Seed9HighChunk8.extended_isPGroup 5) le_sup_left (S8Seed9HighChunk8.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 6)
      (S8Seed9HighChunk8.extended_isPGroup 6) le_sup_left (S8Seed9HighChunk8.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 7)
      (S8Seed9HighChunk8.extended_isPGroup 7) le_sup_left (S8Seed9HighChunk8.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 8)
      (S8Seed9HighChunk8.extended_isPGroup 8) le_sup_left (S8Seed9HighChunk8.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 9)
      (S8Seed9HighChunk8.extended_isPGroup 9) le_sup_left (S8Seed9HighChunk8.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 10)
      (S8Seed9HighChunk8.extended_isPGroup 10) le_sup_left (S8Seed9HighChunk8.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 11)
      (S8Seed9HighChunk8.extended_isPGroup 11) le_sup_left (S8Seed9HighChunk8.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk8.extended_le_adjoin 12)
      (S8Seed9HighChunk8.extended_isPGroup 12) le_sup_left (S8Seed9HighChunk8.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 0)
      (S8Seed9HighChunk9.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk9.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 1)
      (S8Seed9HighChunk9.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk9.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 2)
      (S8Seed9HighChunk9.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk9.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 3)
      (S8Seed9HighChunk9.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk9.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 4)
      (S8Seed9HighChunk9.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk9.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 5)
      (S8Seed9HighChunk9.extended_isPGroup 5) le_sup_left (S8Seed9HighChunk9.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 6)
      (S8Seed9HighChunk9.extended_isPGroup 6) le_sup_left (S8Seed9HighChunk9.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 7)
      (S8Seed9HighChunk9.extended_isPGroup 7) le_sup_left (S8Seed9HighChunk9.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 8)
      (S8Seed9HighChunk9.extended_isPGroup 8) le_sup_left (S8Seed9HighChunk9.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 9)
      (S8Seed9HighChunk9.extended_isPGroup 9) le_sup_left (S8Seed9HighChunk9.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 10)
      (S8Seed9HighChunk9.extended_isPGroup 10) le_sup_left (S8Seed9HighChunk9.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 11)
      (S8Seed9HighChunk9.extended_isPGroup 11) le_sup_left (S8Seed9HighChunk9.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk9.extended_le_adjoin 12)
      (S8Seed9HighChunk9.extended_isPGroup 12) le_sup_left (S8Seed9HighChunk9.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 0)
      (S8Seed9HighChunk10.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk10.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 1)
      (S8Seed9HighChunk10.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk10.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 2)
      (S8Seed9HighChunk10.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk10.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 3)
      (S8Seed9HighChunk10.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk10.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 4)
      (S8Seed9HighChunk10.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk10.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 5)
      (S8Seed9HighChunk10.extended_isPGroup 5) le_sup_left (S8Seed9HighChunk10.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 6)
      (S8Seed9HighChunk10.extended_isPGroup 6) le_sup_left (S8Seed9HighChunk10.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 7)
      (S8Seed9HighChunk10.extended_isPGroup 7) le_sup_left (S8Seed9HighChunk10.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 8)
      (S8Seed9HighChunk10.extended_isPGroup 8) le_sup_left (S8Seed9HighChunk10.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 9)
      (S8Seed9HighChunk10.extended_isPGroup 9) le_sup_left (S8Seed9HighChunk10.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 10)
      (S8Seed9HighChunk10.extended_isPGroup 10) le_sup_left (S8Seed9HighChunk10.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 11)
      (S8Seed9HighChunk10.extended_isPGroup 11) le_sup_left (S8Seed9HighChunk10.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk10.extended_le_adjoin 12)
      (S8Seed9HighChunk10.extended_isPGroup 12) le_sup_left (S8Seed9HighChunk10.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 0)
      (S8Seed9HighChunk11.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk11.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 1)
      (S8Seed9HighChunk11.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk11.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 2)
      (S8Seed9HighChunk11.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk11.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 3)
      (S8Seed9HighChunk11.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk11.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 4)
      (S8Seed9HighChunk11.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk11.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 5)
      (S8Seed9HighChunk11.extended_isPGroup 5) le_sup_left (S8Seed9HighChunk11.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 6)
      (S8Seed9HighChunk11.extended_isPGroup 6) le_sup_left (S8Seed9HighChunk11.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 7)
      (S8Seed9HighChunk11.extended_isPGroup 7) le_sup_left (S8Seed9HighChunk11.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 8)
      (S8Seed9HighChunk11.extended_isPGroup 8) le_sup_left (S8Seed9HighChunk11.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 9)
      (S8Seed9HighChunk11.extended_isPGroup 9) le_sup_left (S8Seed9HighChunk11.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 10)
      (S8Seed9HighChunk11.extended_isPGroup 10) le_sup_left (S8Seed9HighChunk11.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 11)
      (S8Seed9HighChunk11.extended_isPGroup 11) le_sup_left (S8Seed9HighChunk11.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk11.extended_le_adjoin 12)
      (S8Seed9HighChunk11.extended_isPGroup 12) le_sup_left (S8Seed9HighChunk11.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk12.extended_le_adjoin 0)
      (S8Seed9HighChunk12.extended_isPGroup 0) le_sup_left (S8Seed9HighChunk12.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk12.extended_le_adjoin 1)
      (S8Seed9HighChunk12.extended_isPGroup 1) le_sup_left (S8Seed9HighChunk12.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk12.extended_le_adjoin 2)
      (S8Seed9HighChunk12.extended_isPGroup 2) le_sup_left (S8Seed9HighChunk12.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk12.extended_le_adjoin 3)
      (S8Seed9HighChunk12.extended_isPGroup 3) le_sup_left (S8Seed9HighChunk12.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed9HighChunk12.extended_le_adjoin 4)
      (S8Seed9HighChunk12.extended_isPGroup 4) le_sup_left (S8Seed9HighChunk12.extended_card_gt 4))

theorem adjoin_property (g : Ambient) : LowOrEscape (H ⊔ Subgroup.closure {g}) := by
  obtain ⟨i, hi⟩ := S8Seed9LeftCosets.covers g
  have he := FiniteLeftCosetCover.adjoin_eq_of_same_left_coset
    (H := H) g (representatives i) hi
  have hp := S8Seed9NormalizerRoots.reduction.edge_property_representative
    LowOrEscape (by
      intro a ha W hW
      change LowOrEscape (MulAut.conj
        (S8Seed9NormalizerRoots.edgeConjugator (S8Seed9NormalizerRoots.letters a)) • W)
      exact edge_property _ W hW) root_property i
  rw [← he] at hp
  exact hp

theorem low_join_1_2 : Escape (rows 1 ⊔ rows 2) :=
  escape_of_extension _ _ S8Seed9LowJoin1_2.extended_le_join
    S8Seed9LowJoin1_2.extended_isPGroup le_sup_left
    S8Seed9LowJoin1_2.extended_card_gt

theorem low_join_1_3 : Escape (rows 1 ⊔ rows 3) :=
  escape_of_extension _ _ S8Seed9LowJoin1_3.extended_le_join
    S8Seed9LowJoin1_3.extended_isPGroup le_sup_left
    S8Seed9LowJoin1_3.extended_card_gt

theorem low_join_1_4 : Escape (rows 1 ⊔ rows 4) :=
  escape_of_extension _ _ S8Seed9LowJoin1_4.extended_le_join
    S8Seed9LowJoin1_4.extended_isPGroup le_sup_left
    S8Seed9LowJoin1_4.extended_card_gt

theorem low_join_2_4 : Escape (rows 2 ⊔ rows 4) :=
  escape_of_extension _ _ S8Seed9LowJoin2_4.extended_le_join
    S8Seed9LowJoin2_4.extended_isPGroup le_sup_left
    S8Seed9LowJoin2_4.extended_card_gt

theorem low_join_3_4 : Escape (rows 3 ⊔ rows 4) := by
  have h := PermutationPrimePowerSeedEscape.conjugate 2 16
    S8Seed9NormalizerRoots.normalizer (rows 1 ⊔ rows 2) low_join_1_2
  rw [Subgroup.smul_sup,S8Seed9LowRelations.normalizer_one,
    S8Seed9LowRelations.normalizer_two] at h
  exact h

theorem low_join_2_3 : Escape (rows 2 ⊔ rows 3) := by
  have h := PermutationPrimePowerSeedEscape.conjugate 2 16
    S8Seed9NormalizerRoots.normalizer (rows 1 ⊔ rows 4) low_join_1_4
  rw [Subgroup.smul_sup,S8Seed9LowRelations.normalizer_one,
    S8Seed9LowRelations.normalizer_four] at h
  simpa only [sup_comm] using h

theorem join_property (i j : Fin 5) : LowOrEscape (rows i ⊔ rows j) := by
  fin_cases i <;> fin_cases j
  · exact Or.inl ⟨0,sup_idem _⟩
  · exact Or.inl ⟨1,sup_eq_right.mpr (by change rows 0 ≤ rows 1; rw [rows_zero]; exact seed_le 1)⟩
  · exact Or.inl ⟨2,sup_eq_right.mpr (by change rows 0 ≤ rows 2; rw [rows_zero]; exact seed_le 2)⟩
  · exact Or.inl ⟨3,sup_eq_right.mpr (by change rows 0 ≤ rows 3; rw [rows_zero]; exact seed_le 3)⟩
  · exact Or.inl ⟨4,sup_eq_right.mpr (by change rows 0 ≤ rows 4; rw [rows_zero]; exact seed_le 4)⟩
  · exact Or.inl ⟨1,sup_eq_left.mpr (by change rows 0 ≤ rows 1; rw [rows_zero]; exact seed_le 1)⟩
  · exact Or.inl ⟨1,sup_idem _⟩
  · exact Or.inr low_join_1_2
  · exact Or.inr low_join_1_3
  · exact Or.inr low_join_1_4
  · exact Or.inl ⟨2,sup_eq_left.mpr (by change rows 0 ≤ rows 2; rw [rows_zero]; exact seed_le 2)⟩
  · rw [sup_comm]
    exact Or.inr low_join_1_2
  · exact Or.inl ⟨2,sup_idem _⟩
  · exact Or.inr low_join_2_3
  · exact Or.inr low_join_2_4
  · exact Or.inl ⟨3,sup_eq_left.mpr (by change rows 0 ≤ rows 3; rw [rows_zero]; exact seed_le 3)⟩
  · rw [sup_comm]
    exact Or.inr low_join_1_3
  · rw [sup_comm]
    exact Or.inr low_join_2_3
  · exact Or.inl ⟨3,sup_idem _⟩
  · exact Or.inr low_join_3_4
  · exact Or.inl ⟨4,sup_eq_left.mpr (by change rows 0 ≤ rows 4; rw [rows_zero]; exact seed_le 4)⟩
  · rw [sup_comm]
    exact Or.inr low_join_1_4
  · rw [sup_comm]
    exact Or.inr low_join_2_4
  · rw [sup_comm]
    exact Or.inr low_join_3_4
  · exact Or.inl ⟨4,sup_idem _⟩

theorem complete (U : Subgroup Ambient) (hHU : H ≤ U) : LowOrEscape U :=
  FiniteSeedJoinEscapePropertyCoverage.complete_above H Escape
    (fun V W hVW hV => PermutationPrimePowerSeedEscape.mono 2 16 V W hVW hV)
    rows seed_le ⟨0, rows_zero⟩ adjoin_property join_property U hHU

theorem low_or_escape_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) :
    (∃ i : Fin 5, ∃ d : Ambient, MulAut.conj d • U = rows i) ∨ Escape U := by
  have hHU : H ≤ MulAut.conj c • U := by
    rw [← hc]
    change Q.map (MulAut.conj c).toMonoidHom ≤ U.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hQU
  rcases complete (MulAut.conj c • U) hHU with ⟨i, hi⟩ | hescape
  · exact Or.inl ⟨i, c, hi⟩
  · right
    have h := PermutationPrimePowerSeedEscape.conjugate 2 16 c⁻¹ _ hescape
    simpa only [map_inv, inv_smul_smul] using h

end SymmetricSubgroupAsymptotics.S8Seed9OvergroupCoverage
end
