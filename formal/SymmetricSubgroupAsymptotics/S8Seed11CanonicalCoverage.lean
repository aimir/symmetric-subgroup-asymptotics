import SymmetricSubgroupAsymptotics.PermutationPrimePowerSeedEscape
import SymmetricSubgroupAsymptotics.BinaryEightSeed11Transitivity
import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.S8AboveSixteenBinarySeedCanonicalCoverage
import SymmetricSubgroupAsymptotics.S8Seed11HighChunk0
import SymmetricSubgroupAsymptotics.S8Seed11HighChunk1
import SymmetricSubgroupAsymptotics.S8Seed11HighChunk2
import SymmetricSubgroupAsymptotics.S8Seed11HighChunk3
import SymmetricSubgroupAsymptotics.S8Seed11HighChunk4
import SymmetricSubgroupAsymptotics.S8Seed11HighChunk5
import SymmetricSubgroupAsymptotics.S8Seed11HighChunk6
import SymmetricSubgroupAsymptotics.S8Seed11HighChunk7
import SymmetricSubgroupAsymptotics.S8Seed11HighChunk8

/-! Actual overgroups above original8T11. Every proper adjunction has an
ordinary-word certified larger binary subgroup. That subgroup retains its
actual original-point action throughout transport and registry dispatch. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed11CanonicalCoverage
open S8Seed11LeftCosets

abbrev Escape (W : Subgroup Ambient) : Prop :=
  PermutationPrimePowerSeedEscape.ContainsAbove 2 16 W

def EqSeedOrEscape (W : Subgroup Ambient) : Prop := W = H ∨ Escape W

theorem escape_of_extension (P W : Subgroup Ambient) (hPW : P ≤ W)
    (hP : IsPGroup 2 P) (hHP : H ≤ P) (hcard : 16 < Nat.card P) : Escape W :=
  ⟨P, hPW, hP,
    permutationSubgroupTransitive_mono H P hHP BinaryEightSeed11Transitivity.transitive,
    hcard⟩

theorem root_property (k : Fin 108) : EqSeedOrEscape
    (H ⊔ Subgroup.closure {representatives (S8Seed11NormalizerRoots.roots k)}) := by
  fin_cases k
  · exact Or.inl S8Seed11NormalizerRoots.root_zero_eq_seed
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 0)
      (S8Seed11HighChunk0.extended_isPGroup 0) le_sup_left (S8Seed11HighChunk0.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 1)
      (S8Seed11HighChunk0.extended_isPGroup 1) le_sup_left (S8Seed11HighChunk0.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 2)
      (S8Seed11HighChunk0.extended_isPGroup 2) le_sup_left (S8Seed11HighChunk0.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 3)
      (S8Seed11HighChunk0.extended_isPGroup 3) le_sup_left (S8Seed11HighChunk0.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 4)
      (S8Seed11HighChunk0.extended_isPGroup 4) le_sup_left (S8Seed11HighChunk0.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 5)
      (S8Seed11HighChunk0.extended_isPGroup 5) le_sup_left (S8Seed11HighChunk0.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 6)
      (S8Seed11HighChunk0.extended_isPGroup 6) le_sup_left (S8Seed11HighChunk0.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 7)
      (S8Seed11HighChunk0.extended_isPGroup 7) le_sup_left (S8Seed11HighChunk0.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 8)
      (S8Seed11HighChunk0.extended_isPGroup 8) le_sup_left (S8Seed11HighChunk0.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 9)
      (S8Seed11HighChunk0.extended_isPGroup 9) le_sup_left (S8Seed11HighChunk0.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 10)
      (S8Seed11HighChunk0.extended_isPGroup 10) le_sup_left (S8Seed11HighChunk0.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 11)
      (S8Seed11HighChunk0.extended_isPGroup 11) le_sup_left (S8Seed11HighChunk0.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk0.extended_le_adjoin 12)
      (S8Seed11HighChunk0.extended_isPGroup 12) le_sup_left (S8Seed11HighChunk0.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 0)
      (S8Seed11HighChunk1.extended_isPGroup 0) le_sup_left (S8Seed11HighChunk1.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 1)
      (S8Seed11HighChunk1.extended_isPGroup 1) le_sup_left (S8Seed11HighChunk1.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 2)
      (S8Seed11HighChunk1.extended_isPGroup 2) le_sup_left (S8Seed11HighChunk1.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 3)
      (S8Seed11HighChunk1.extended_isPGroup 3) le_sup_left (S8Seed11HighChunk1.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 4)
      (S8Seed11HighChunk1.extended_isPGroup 4) le_sup_left (S8Seed11HighChunk1.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 5)
      (S8Seed11HighChunk1.extended_isPGroup 5) le_sup_left (S8Seed11HighChunk1.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 6)
      (S8Seed11HighChunk1.extended_isPGroup 6) le_sup_left (S8Seed11HighChunk1.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 7)
      (S8Seed11HighChunk1.extended_isPGroup 7) le_sup_left (S8Seed11HighChunk1.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 8)
      (S8Seed11HighChunk1.extended_isPGroup 8) le_sup_left (S8Seed11HighChunk1.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 9)
      (S8Seed11HighChunk1.extended_isPGroup 9) le_sup_left (S8Seed11HighChunk1.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 10)
      (S8Seed11HighChunk1.extended_isPGroup 10) le_sup_left (S8Seed11HighChunk1.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 11)
      (S8Seed11HighChunk1.extended_isPGroup 11) le_sup_left (S8Seed11HighChunk1.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk1.extended_le_adjoin 12)
      (S8Seed11HighChunk1.extended_isPGroup 12) le_sup_left (S8Seed11HighChunk1.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 0)
      (S8Seed11HighChunk2.extended_isPGroup 0) le_sup_left (S8Seed11HighChunk2.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 1)
      (S8Seed11HighChunk2.extended_isPGroup 1) le_sup_left (S8Seed11HighChunk2.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 2)
      (S8Seed11HighChunk2.extended_isPGroup 2) le_sup_left (S8Seed11HighChunk2.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 3)
      (S8Seed11HighChunk2.extended_isPGroup 3) le_sup_left (S8Seed11HighChunk2.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 4)
      (S8Seed11HighChunk2.extended_isPGroup 4) le_sup_left (S8Seed11HighChunk2.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 5)
      (S8Seed11HighChunk2.extended_isPGroup 5) le_sup_left (S8Seed11HighChunk2.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 6)
      (S8Seed11HighChunk2.extended_isPGroup 6) le_sup_left (S8Seed11HighChunk2.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 7)
      (S8Seed11HighChunk2.extended_isPGroup 7) le_sup_left (S8Seed11HighChunk2.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 8)
      (S8Seed11HighChunk2.extended_isPGroup 8) le_sup_left (S8Seed11HighChunk2.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 9)
      (S8Seed11HighChunk2.extended_isPGroup 9) le_sup_left (S8Seed11HighChunk2.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 10)
      (S8Seed11HighChunk2.extended_isPGroup 10) le_sup_left (S8Seed11HighChunk2.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 11)
      (S8Seed11HighChunk2.extended_isPGroup 11) le_sup_left (S8Seed11HighChunk2.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk2.extended_le_adjoin 12)
      (S8Seed11HighChunk2.extended_isPGroup 12) le_sup_left (S8Seed11HighChunk2.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 0)
      (S8Seed11HighChunk3.extended_isPGroup 0) le_sup_left (S8Seed11HighChunk3.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 1)
      (S8Seed11HighChunk3.extended_isPGroup 1) le_sup_left (S8Seed11HighChunk3.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 2)
      (S8Seed11HighChunk3.extended_isPGroup 2) le_sup_left (S8Seed11HighChunk3.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 3)
      (S8Seed11HighChunk3.extended_isPGroup 3) le_sup_left (S8Seed11HighChunk3.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 4)
      (S8Seed11HighChunk3.extended_isPGroup 4) le_sup_left (S8Seed11HighChunk3.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 5)
      (S8Seed11HighChunk3.extended_isPGroup 5) le_sup_left (S8Seed11HighChunk3.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 6)
      (S8Seed11HighChunk3.extended_isPGroup 6) le_sup_left (S8Seed11HighChunk3.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 7)
      (S8Seed11HighChunk3.extended_isPGroup 7) le_sup_left (S8Seed11HighChunk3.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 8)
      (S8Seed11HighChunk3.extended_isPGroup 8) le_sup_left (S8Seed11HighChunk3.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 9)
      (S8Seed11HighChunk3.extended_isPGroup 9) le_sup_left (S8Seed11HighChunk3.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 10)
      (S8Seed11HighChunk3.extended_isPGroup 10) le_sup_left (S8Seed11HighChunk3.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 11)
      (S8Seed11HighChunk3.extended_isPGroup 11) le_sup_left (S8Seed11HighChunk3.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk3.extended_le_adjoin 12)
      (S8Seed11HighChunk3.extended_isPGroup 12) le_sup_left (S8Seed11HighChunk3.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 0)
      (S8Seed11HighChunk4.extended_isPGroup 0) le_sup_left (S8Seed11HighChunk4.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 1)
      (S8Seed11HighChunk4.extended_isPGroup 1) le_sup_left (S8Seed11HighChunk4.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 2)
      (S8Seed11HighChunk4.extended_isPGroup 2) le_sup_left (S8Seed11HighChunk4.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 3)
      (S8Seed11HighChunk4.extended_isPGroup 3) le_sup_left (S8Seed11HighChunk4.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 4)
      (S8Seed11HighChunk4.extended_isPGroup 4) le_sup_left (S8Seed11HighChunk4.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 5)
      (S8Seed11HighChunk4.extended_isPGroup 5) le_sup_left (S8Seed11HighChunk4.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 6)
      (S8Seed11HighChunk4.extended_isPGroup 6) le_sup_left (S8Seed11HighChunk4.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 7)
      (S8Seed11HighChunk4.extended_isPGroup 7) le_sup_left (S8Seed11HighChunk4.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 8)
      (S8Seed11HighChunk4.extended_isPGroup 8) le_sup_left (S8Seed11HighChunk4.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 9)
      (S8Seed11HighChunk4.extended_isPGroup 9) le_sup_left (S8Seed11HighChunk4.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 10)
      (S8Seed11HighChunk4.extended_isPGroup 10) le_sup_left (S8Seed11HighChunk4.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 11)
      (S8Seed11HighChunk4.extended_isPGroup 11) le_sup_left (S8Seed11HighChunk4.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk4.extended_le_adjoin 12)
      (S8Seed11HighChunk4.extended_isPGroup 12) le_sup_left (S8Seed11HighChunk4.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 0)
      (S8Seed11HighChunk5.extended_isPGroup 0) le_sup_left (S8Seed11HighChunk5.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 1)
      (S8Seed11HighChunk5.extended_isPGroup 1) le_sup_left (S8Seed11HighChunk5.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 2)
      (S8Seed11HighChunk5.extended_isPGroup 2) le_sup_left (S8Seed11HighChunk5.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 3)
      (S8Seed11HighChunk5.extended_isPGroup 3) le_sup_left (S8Seed11HighChunk5.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 4)
      (S8Seed11HighChunk5.extended_isPGroup 4) le_sup_left (S8Seed11HighChunk5.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 5)
      (S8Seed11HighChunk5.extended_isPGroup 5) le_sup_left (S8Seed11HighChunk5.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 6)
      (S8Seed11HighChunk5.extended_isPGroup 6) le_sup_left (S8Seed11HighChunk5.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 7)
      (S8Seed11HighChunk5.extended_isPGroup 7) le_sup_left (S8Seed11HighChunk5.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 8)
      (S8Seed11HighChunk5.extended_isPGroup 8) le_sup_left (S8Seed11HighChunk5.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 9)
      (S8Seed11HighChunk5.extended_isPGroup 9) le_sup_left (S8Seed11HighChunk5.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 10)
      (S8Seed11HighChunk5.extended_isPGroup 10) le_sup_left (S8Seed11HighChunk5.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 11)
      (S8Seed11HighChunk5.extended_isPGroup 11) le_sup_left (S8Seed11HighChunk5.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk5.extended_le_adjoin 12)
      (S8Seed11HighChunk5.extended_isPGroup 12) le_sup_left (S8Seed11HighChunk5.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 0)
      (S8Seed11HighChunk6.extended_isPGroup 0) le_sup_left (S8Seed11HighChunk6.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 1)
      (S8Seed11HighChunk6.extended_isPGroup 1) le_sup_left (S8Seed11HighChunk6.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 2)
      (S8Seed11HighChunk6.extended_isPGroup 2) le_sup_left (S8Seed11HighChunk6.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 3)
      (S8Seed11HighChunk6.extended_isPGroup 3) le_sup_left (S8Seed11HighChunk6.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 4)
      (S8Seed11HighChunk6.extended_isPGroup 4) le_sup_left (S8Seed11HighChunk6.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 5)
      (S8Seed11HighChunk6.extended_isPGroup 5) le_sup_left (S8Seed11HighChunk6.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 6)
      (S8Seed11HighChunk6.extended_isPGroup 6) le_sup_left (S8Seed11HighChunk6.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 7)
      (S8Seed11HighChunk6.extended_isPGroup 7) le_sup_left (S8Seed11HighChunk6.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 8)
      (S8Seed11HighChunk6.extended_isPGroup 8) le_sup_left (S8Seed11HighChunk6.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 9)
      (S8Seed11HighChunk6.extended_isPGroup 9) le_sup_left (S8Seed11HighChunk6.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 10)
      (S8Seed11HighChunk6.extended_isPGroup 10) le_sup_left (S8Seed11HighChunk6.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 11)
      (S8Seed11HighChunk6.extended_isPGroup 11) le_sup_left (S8Seed11HighChunk6.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk6.extended_le_adjoin 12)
      (S8Seed11HighChunk6.extended_isPGroup 12) le_sup_left (S8Seed11HighChunk6.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 0)
      (S8Seed11HighChunk7.extended_isPGroup 0) le_sup_left (S8Seed11HighChunk7.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 1)
      (S8Seed11HighChunk7.extended_isPGroup 1) le_sup_left (S8Seed11HighChunk7.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 2)
      (S8Seed11HighChunk7.extended_isPGroup 2) le_sup_left (S8Seed11HighChunk7.extended_card_gt 2))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 3)
      (S8Seed11HighChunk7.extended_isPGroup 3) le_sup_left (S8Seed11HighChunk7.extended_card_gt 3))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 4)
      (S8Seed11HighChunk7.extended_isPGroup 4) le_sup_left (S8Seed11HighChunk7.extended_card_gt 4))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 5)
      (S8Seed11HighChunk7.extended_isPGroup 5) le_sup_left (S8Seed11HighChunk7.extended_card_gt 5))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 6)
      (S8Seed11HighChunk7.extended_isPGroup 6) le_sup_left (S8Seed11HighChunk7.extended_card_gt 6))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 7)
      (S8Seed11HighChunk7.extended_isPGroup 7) le_sup_left (S8Seed11HighChunk7.extended_card_gt 7))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 8)
      (S8Seed11HighChunk7.extended_isPGroup 8) le_sup_left (S8Seed11HighChunk7.extended_card_gt 8))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 9)
      (S8Seed11HighChunk7.extended_isPGroup 9) le_sup_left (S8Seed11HighChunk7.extended_card_gt 9))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 10)
      (S8Seed11HighChunk7.extended_isPGroup 10) le_sup_left (S8Seed11HighChunk7.extended_card_gt 10))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 11)
      (S8Seed11HighChunk7.extended_isPGroup 11) le_sup_left (S8Seed11HighChunk7.extended_card_gt 11))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk7.extended_le_adjoin 12)
      (S8Seed11HighChunk7.extended_isPGroup 12) le_sup_left (S8Seed11HighChunk7.extended_card_gt 12))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk8.extended_le_adjoin 0)
      (S8Seed11HighChunk8.extended_isPGroup 0) le_sup_left (S8Seed11HighChunk8.extended_card_gt 0))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk8.extended_le_adjoin 1)
      (S8Seed11HighChunk8.extended_isPGroup 1) le_sup_left (S8Seed11HighChunk8.extended_card_gt 1))
  · exact Or.inr (escape_of_extension _ _ (S8Seed11HighChunk8.extended_le_adjoin 2)
      (S8Seed11HighChunk8.extended_isPGroup 2) le_sup_left (S8Seed11HighChunk8.extended_card_gt 2))

theorem property_conjugate (c : Ambient) (hc : MulAut.conj c • H = H)
    (W : Subgroup Ambient) (hW : EqSeedOrEscape W) :
    EqSeedOrEscape (MulAut.conj c • W) := by
  rcases hW with rfl | hescape
  · exact Or.inl hc
  · exact Or.inr (PermutationPrimePowerSeedEscape.conjugate 2 16 c W hescape)

theorem adjoin_property (g : Ambient) : EqSeedOrEscape (H ⊔ Subgroup.closure {g}) := by
  obtain ⟨i, hi⟩ := S8Seed11LeftCosets.covers g
  have he := FiniteLeftCosetCover.adjoin_eq_of_same_left_coset
    (H := H) g (representatives i) hi
  have hp := S8Seed11NormalizerRoots.reduction.property_representative
    EqSeedOrEscape property_conjugate root_property i
  rw [← he] at hp
  exact hp

theorem complete (U : Subgroup Ambient) (hHU : H ≤ U) : U = H ∨ Escape U := by
  classical
  by_cases heq : U = H
  · exact Or.inl heq
  · right
    have hnot : ¬ U ≤ H := fun h => heq (le_antisymm h hHU)
    obtain ⟨g, hgU, hgH⟩ := Set.not_subset.mp hnot
    rcases adjoin_property g with heq | hescape
    · have hg : g ∈ H ⊔ Subgroup.closure {g} :=
        (show Subgroup.closure {g} ≤ H ⊔ Subgroup.closure {g} from le_sup_right)
          (Subgroup.subset_closure (by simp))
      exact False.elim (hgH (heq ▸ hg))
    · apply PermutationPrimePowerSeedEscape.mono 2 16 _ U _ hescape
      refine sup_le hHU ((Subgroup.closure_le U).mpr ?_)
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hgU

theorem overgroup_complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) : U = Q ∨ Escape U := by
  have hHU : H ≤ MulAut.conj c • U := by
    rw [← hc]
    change Q.map (MulAut.conj c).toMonoidHom ≤ U.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hQU
  rcases complete (MulAut.conj c • U) hHU with heq | hescape
  · left
    have hsame : MulAut.conj c • U = MulAut.conj c • Q := heq.trans hc.symm
    have h := congrArg (fun W : Subgroup Ambient => MulAut.conj c⁻¹ • W) hsame
    simpa only [map_inv, inv_smul_smul] using h
  · right
    have h := PermutationPrimePowerSeedEscape.conjugate 2 16 c⁻¹ _ hescape
    simpa only [map_inv, inv_smul_smul] using h

theorem seed_isPGroup : IsPGroup 2 H :=
  IsPGroup.of_card (n := 4) BinaryMenuCayley8T11.exact_card

theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬ IsPGroup 2 U) :
    ∃ i : Fin 24, ∃ d : Ambient,
      MulAut.conj d • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  rcases overgroup_complete_of_conjugate U Q hQU c hc with heq | ⟨P, hPU, hp, ht, hcard⟩
  · have hp : IsPGroup 2 U := by
      rw [heq]
      exact S8CanonicalNonbinaryTransport.isPGroup_of_conjugate Q H c hc seed_isPGroup
    exact False.elim (hnot hp)
  · exact S8AboveSixteenBinarySeedCanonicalCoverage.complete U P hPU hp ht hcard hnot

end SymmetricSubgroupAsymptotics.S8Seed11CanonicalCoverage
end
