import SymmetricSubgroupAsymptotics.FiniteSeedAtomJoinRows
import SymmetricSubgroupAsymptotics.S8Seed4LowNormalizer1
import SymmetricSubgroupAsymptotics.S8Seed4LowNormalizer2
import SymmetricSubgroupAsymptotics.S8Seed4LowNormalizer3
import SymmetricSubgroupAsymptotics.S8Seed4LowNormalizer4
import SymmetricSubgroupAsymptotics.S8Seed4LowNormalizer6
import SymmetricSubgroupAsymptotics.S8Seed4LowNormalizer8
import SymmetricSubgroupAsymptotics.S8Seed4LowJoin2_4
import SymmetricSubgroupAsymptotics.S8Seed4LowJoin4_6
import SymmetricSubgroupAsymptotics.S8Seed4LowJoin2_6Escape
import SymmetricSubgroupAsymptotics.S8Seed4LowJoin4_8Escape
import SymmetricSubgroupAsymptotics.BinaryEightSeed4Transitivity
import SymmetricSubgroupAsymptotics.PermutationPrimePowerSeedEscape
import Mathlib.Data.Fintype.Powerset

/-! Four actual order-24 atoms form a square. Adjacent joins are the four
displayed low rows; either opposite pair contains an actual larger binary
subgroup. Finite joins and normalizer transport retain original points. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed4AtomRows
open S8Seed4LeftCosets S8Seed4LowModels

abbrev Escape (W : Subgroup Ambient) : Prop :=
  PermutationPrimePowerSeedEscape.ContainsAbove 2 8 W

def atoms : Fin 4 → Subgroup Ambient := ![rows 2, rows 4, rows 6, rows 8]
def joined (s : Finset (Fin 4)) : Subgroup Ambient :=
  FiniteSeedAtomJoinRows.rows H atoms s

theorem seed_le_atom (i : Fin 4) : H ≤ atoms i := by
  fin_cases i
  · exact seed_le 2
  · exact seed_le 4
  · exact seed_le 6
  · exact seed_le 8

theorem joined_empty : joined ∅ = rows 0 :=
  (FiniteSeedAtomJoinRows.empty H atoms).trans rows_zero.symm

theorem joined_singleton (i : Fin 4) : joined {i} = atoms i := by
  simp only [joined, FiniteSeedAtomJoinRows.rows, Finset.sup_singleton]
  exact sup_eq_right.mpr (seed_le_atom i)

theorem joined_union (s t : Finset (Fin 4)) : joined s ⊔ joined t = joined (s ∪ t) :=
  FiniteSeedAtomJoinRows.union H atoms s t

theorem join2_8 : rows 2 ⊔ rows 8 = rows 7 := by
  have h := congrArg (fun W : Subgroup Ambient =>
    MulAut.conj S8Seed4NormalizerRoots.normalizer • W) S8Seed4LowJoin2_4.join_eq
  dsimp only at h
  rw [Subgroup.smul_sup, S8Seed4LowNormalizer2.normalizer_image,
    S8Seed4LowNormalizer4.normalizer_image, S8Seed4LowNormalizer1.normalizer_image] at h
  exact h

theorem join6_8 : rows 6 ⊔ rows 8 = rows 5 := by
  have h := congrArg (fun W : Subgroup Ambient =>
    MulAut.conj S8Seed4NormalizerRoots.normalizer • W) S8Seed4LowJoin4_6.join_eq
  dsimp only at h
  rw [Subgroup.smul_sup, S8Seed4LowNormalizer4.normalizer_image,
    S8Seed4LowNormalizer6.normalizer_image, S8Seed4LowNormalizer3.normalizer_image] at h
  simpa only [sup_comm] using h

theorem joined_pair01 : joined {0, 1} = rows 1 := by
  have h := joined_union {0} {1}
  rw [Finset.singleton_union, joined_singleton, joined_singleton] at h
  change rows 2 ⊔ rows 4 = joined {0, 1} at h
  exact h.symm.trans S8Seed4LowJoin2_4.join_eq

theorem joined_pair12 : joined {1, 2} = rows 3 := by
  have h := joined_union {1} {2}
  rw [Finset.singleton_union, joined_singleton, joined_singleton] at h
  change rows 4 ⊔ rows 6 = joined {1, 2} at h
  exact h.symm.trans S8Seed4LowJoin4_6.join_eq

theorem joined_pair23 : joined {2, 3} = rows 5 := by
  have h := joined_union {2} {3}
  rw [Finset.singleton_union, joined_singleton, joined_singleton] at h
  change rows 6 ⊔ rows 8 = joined {2, 3} at h
  exact h.symm.trans join6_8

theorem joined_pair03 : joined {0, 3} = rows 7 := by
  have h := joined_union {0} {3}
  rw [Finset.singleton_union, joined_singleton, joined_singleton] at h
  change rows 2 ⊔ rows 8 = joined {0, 3} at h
  exact h.symm.trans join2_8

def atomPermutation : Fin 4 → Fin 4 := ![0, 3, 2, 1]

theorem conjugates_atoms (i : Fin 4) :
    MulAut.conj S8Seed4NormalizerRoots.normalizer • atoms i = atoms (atomPermutation i) := by
  fin_cases i
  · exact S8Seed4LowNormalizer2.normalizer_image
  · exact S8Seed4LowNormalizer4.normalizer_image
  · exact S8Seed4LowNormalizer6.normalizer_image
  · exact S8Seed4LowNormalizer8.normalizer_image

theorem conjugates_joined (s : Finset (Fin 4)) :
    MulAut.conj S8Seed4NormalizerRoots.normalizer • joined s = joined (s.image atomPermutation) :=
  FiniteSeedAtomJoinRows.conjugated H atoms S8Seed4NormalizerRoots.normalizer
    atomPermutation S8Seed4NormalizerRoots.normalizes_seed conjugates_atoms s

theorem model_is_joined (i : Fin 9) : ∃ s : Finset (Fin 4), rows i = joined s := by
  fin_cases i
  · exact ⟨∅, joined_empty.symm⟩
  · exact ⟨{0, 1}, joined_pair01.symm⟩
  · exact ⟨{0}, (joined_singleton 0).symm⟩
  · exact ⟨{1, 2}, joined_pair12.symm⟩
  · exact ⟨{1}, (joined_singleton 1).symm⟩
  · exact ⟨{2, 3}, joined_pair23.symm⟩
  · exact ⟨{2}, (joined_singleton 2).symm⟩
  · exact ⟨{0, 3}, joined_pair03.symm⟩
  · exact ⟨{3}, (joined_singleton 3).symm⟩

theorem escape26 : Escape (rows 2 ⊔ rows 6) := by
  refine ⟨S8Seed4LowJoin2_6Escape.extendedSeed,
    S8Seed4LowJoin2_6Escape.extended_le_join,
    S8Seed4LowJoin2_6Escape.extended_isPGroup, ?_,
    S8Seed4LowJoin2_6Escape.extended_card_gt⟩
  exact permutationSubgroupTransitive_mono H _ le_sup_left BinaryEightSeed4Transitivity.transitive

theorem escape48 : Escape (rows 4 ⊔ rows 8) := by
  refine ⟨S8Seed4LowJoin4_8Escape.extendedSeed,
    S8Seed4LowJoin4_8Escape.extended_le_join,
    S8Seed4LowJoin4_8Escape.extended_isPGroup, ?_,
    S8Seed4LowJoin4_8Escape.extended_card_gt⟩
  exact permutationSubgroupTransitive_mono H _ le_sup_left BinaryEightSeed4Transitivity.transitive

theorem atom_le_joined (s : Finset (Fin 4)) (i : Fin 4) (hi : i ∈ s) : atoms i ≤ joined s :=
  (Finset.le_sup hi).trans le_sup_right

theorem joined_is_model_or_escape (s : Finset (Fin 4)) :
    (∃ i : Fin 9, joined s = rows i) ∨ Escape (joined s) := by
  by_cases h02 : (0 : Fin 4) ∈ s ∧ (2 : Fin 4) ∈ s
  · right
    exact PermutationPrimePowerSeedEscape.mono 2 8 _ _
      (sup_le (atom_le_joined s 0 h02.1) (atom_le_joined s 2 h02.2)) escape26
  by_cases h13 : (1 : Fin 4) ∈ s ∧ (3 : Fin 4) ∈ s
  · right
    exact PermutationPrimePowerSeedEscape.mono 2 8 _ _
      (sup_le (atom_le_joined s 1 h13.1) (atom_le_joined s 3 h13.2)) escape48
  left
  by_cases h0 : (0 : Fin 4) ∈ s
  · have h2 : (2 : Fin 4) ∉ s := fun h => h02 ⟨h0, h⟩
    by_cases h1 : (1 : Fin 4) ∈ s
    · have h3 : (3 : Fin 4) ∉ s := fun h => h13 ⟨h1, h⟩
      have hs : s = {0, 1} := by ext i; fin_cases i <;> simp_all
      exact ⟨1, (congrArg joined hs).trans joined_pair01⟩
    · by_cases h3 : (3 : Fin 4) ∈ s
      · have hs : s = {0, 3} := by ext i; fin_cases i <;> simp_all
        exact ⟨7, (congrArg joined hs).trans joined_pair03⟩
      · have hs : s = {0} := by ext i; fin_cases i <;> simp_all
        exact ⟨2, (congrArg joined hs).trans (joined_singleton 0)⟩
  · by_cases h2 : (2 : Fin 4) ∈ s
    · by_cases h1 : (1 : Fin 4) ∈ s
      · have h3 : (3 : Fin 4) ∉ s := fun h => h13 ⟨h1, h⟩
        have hs : s = {1, 2} := by ext i; fin_cases i <;> simp_all
        exact ⟨3, (congrArg joined hs).trans joined_pair12⟩
      · by_cases h3 : (3 : Fin 4) ∈ s
        · have hs : s = {2, 3} := by ext i; fin_cases i <;> simp_all
          exact ⟨5, (congrArg joined hs).trans joined_pair23⟩
        · have hs : s = {2} := by ext i; fin_cases i <;> simp_all
          exact ⟨6, (congrArg joined hs).trans (joined_singleton 2)⟩
    · by_cases h1 : (1 : Fin 4) ∈ s
      · have h3 : (3 : Fin 4) ∉ s := fun h => h13 ⟨h1, h⟩
        have hs : s = {1} := by ext i; fin_cases i <;> simp_all
        exact ⟨4, (congrArg joined hs).trans (joined_singleton 1)⟩
      · by_cases h3 : (3 : Fin 4) ∈ s
        · have hs : s = {3} := by ext i; fin_cases i <;> simp_all
          exact ⟨8, (congrArg joined hs).trans (joined_singleton 3)⟩
        · have hs : s = ∅ := by ext i; fin_cases i <;> simp_all
          exact ⟨0, (congrArg joined hs).trans joined_empty⟩

end SymmetricSubgroupAsymptotics.S8Seed4AtomRows
end
