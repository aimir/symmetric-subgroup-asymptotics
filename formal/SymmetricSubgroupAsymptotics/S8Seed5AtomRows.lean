import SymmetricSubgroupAsymptotics.FiniteSeedAtomJoinRows
import SymmetricSubgroupAsymptotics.S8Seed5LowNormalizer1
import SymmetricSubgroupAsymptotics.S8Seed5LowNormalizer2
import SymmetricSubgroupAsymptotics.S8Seed5LowNormalizer3
import SymmetricSubgroupAsymptotics.S8Seed5LowNormalizer4
import SymmetricSubgroupAsymptotics.S8Seed5LowJoin1_2Escape
import SymmetricSubgroupAsymptotics.S8Seed5LowJoin1_3Escape
import SymmetricSubgroupAsymptotics.S8Seed5LowJoin1_4Escape
import SymmetricSubgroupAsymptotics.S8Seed5LowJoin3_4Escape
import SymmetricSubgroupAsymptotics.BinaryEightSeed5Transitivity
import SymmetricSubgroupAsymptotics.PermutationPrimePowerSeedEscape
import Mathlib.Data.Fintype.Powerset

/-! Four actual low atoms. Any two distinct atoms contain an actual larger
binary subgroup. Four ordinary-word escape packets and normalizer transport
suffice; no low-row order recognition or complete join table is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed5AtomRows
open S8Seed5LeftCosets S8Seed5LowModels

abbrev Escape (W : Subgroup Ambient) : Prop :=
  PermutationPrimePowerSeedEscape.ContainsAbove 2 8 W

def atoms : Fin 4 → Subgroup Ambient := ![rows 1, rows 2, rows 3, rows 4]
def joined (s : Finset (Fin 4)) : Subgroup Ambient :=
  FiniteSeedAtomJoinRows.rows H atoms s

theorem seed_le_atom (i : Fin 4) : H ≤ atoms i := by
  fin_cases i
  · exact seed_le 1
  · exact seed_le 2
  · exact seed_le 3
  · exact seed_le 4

theorem joined_empty : joined ∅ = rows 0 :=
  (FiniteSeedAtomJoinRows.empty H atoms).trans rows_zero.symm

theorem joined_singleton (i : Fin 4) : joined {i} = atoms i := by
  simp only [joined, FiniteSeedAtomJoinRows.rows, Finset.sup_singleton]
  exact sup_eq_right.mpr (seed_le_atom i)

theorem joined_union (s t : Finset (Fin 4)) : joined s ⊔ joined t = joined (s ∪ t) :=
  FiniteSeedAtomJoinRows.union H atoms s t

def atomPermutation : Fin 4 → Fin 4 := ![1, 0, 3, 2]

theorem conjugates_atoms (i : Fin 4) :
    MulAut.conj S8Seed5NormalizerRoots.normalizer • atoms i = atoms (atomPermutation i) := by
  fin_cases i
  · exact S8Seed5LowNormalizer1.normalizer_image
  · exact S8Seed5LowNormalizer2.normalizer_image
  · exact S8Seed5LowNormalizer3.normalizer_image
  · exact S8Seed5LowNormalizer4.normalizer_image

theorem conjugates_joined (s : Finset (Fin 4)) :
    MulAut.conj S8Seed5NormalizerRoots.normalizer • joined s = joined (s.image atomPermutation) :=
  FiniteSeedAtomJoinRows.conjugated H atoms S8Seed5NormalizerRoots.normalizer
    atomPermutation S8Seed5NormalizerRoots.normalizes_seed conjugates_atoms s

theorem model_is_joined (i : Fin 5) : ∃ s : Finset (Fin 4), rows i = joined s := by
  fin_cases i
  · exact ⟨∅, joined_empty.symm⟩
  · exact ⟨{0}, (joined_singleton 0).symm⟩
  · exact ⟨{1}, (joined_singleton 1).symm⟩
  · exact ⟨{2}, (joined_singleton 2).symm⟩
  · exact ⟨{3}, (joined_singleton 3).symm⟩

theorem escape12 : Escape (rows 1 ⊔ rows 2) := by
  refine ⟨S8Seed5LowJoin1_2Escape.extendedSeed,
    S8Seed5LowJoin1_2Escape.extended_le_join,
    S8Seed5LowJoin1_2Escape.extended_isPGroup, ?_,
    S8Seed5LowJoin1_2Escape.extended_card_gt⟩
  exact permutationSubgroupTransitive_mono H _ le_sup_left BinaryEightSeed5Transitivity.transitive

theorem escape13 : Escape (rows 1 ⊔ rows 3) := by
  refine ⟨S8Seed5LowJoin1_3Escape.extendedSeed,
    S8Seed5LowJoin1_3Escape.extended_le_join,
    S8Seed5LowJoin1_3Escape.extended_isPGroup, ?_,
    S8Seed5LowJoin1_3Escape.extended_card_gt⟩
  exact permutationSubgroupTransitive_mono H _ le_sup_left BinaryEightSeed5Transitivity.transitive

theorem escape14 : Escape (rows 1 ⊔ rows 4) := by
  refine ⟨S8Seed5LowJoin1_4Escape.extendedSeed,
    S8Seed5LowJoin1_4Escape.extended_le_join,
    S8Seed5LowJoin1_4Escape.extended_isPGroup, ?_,
    S8Seed5LowJoin1_4Escape.extended_card_gt⟩
  exact permutationSubgroupTransitive_mono H _ le_sup_left BinaryEightSeed5Transitivity.transitive

theorem escape34 : Escape (rows 3 ⊔ rows 4) := by
  refine ⟨S8Seed5LowJoin3_4Escape.extendedSeed,
    S8Seed5LowJoin3_4Escape.extended_le_join,
    S8Seed5LowJoin3_4Escape.extended_isPGroup, ?_,
    S8Seed5LowJoin3_4Escape.extended_card_gt⟩
  exact permutationSubgroupTransitive_mono H _ le_sup_left BinaryEightSeed5Transitivity.transitive

theorem escape23 : Escape (rows 2 ⊔ rows 3) := by
  have h := PermutationPrimePowerSeedEscape.conjugate 2 8
    S8Seed5NormalizerRoots.normalizer _ escape14
  rw [Subgroup.smul_sup, S8Seed5LowNormalizer1.normalizer_image,
    S8Seed5LowNormalizer4.normalizer_image] at h
  exact h

theorem escape24 : Escape (rows 2 ⊔ rows 4) := by
  have h := PermutationPrimePowerSeedEscape.conjugate 2 8
    S8Seed5NormalizerRoots.normalizer _ escape13
  rw [Subgroup.smul_sup, S8Seed5LowNormalizer1.normalizer_image,
    S8Seed5LowNormalizer3.normalizer_image] at h
  exact h

theorem escape_distinct (i j : Fin 4) (hij : i ≠ j) : Escape (atoms i ⊔ atoms j) := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact escape12
  · exact escape13
  · exact escape14
  · change Escape (rows 2 ⊔ rows 1)
    simpa only [sup_comm] using escape12
  · exact (hij rfl).elim
  · exact escape23
  · exact escape24
  · change Escape (rows 3 ⊔ rows 1)
    simpa only [sup_comm] using escape13
  · change Escape (rows 3 ⊔ rows 2)
    simpa only [sup_comm] using escape23
  · exact (hij rfl).elim
  · exact escape34
  · change Escape (rows 4 ⊔ rows 1)
    simpa only [sup_comm] using escape14
  · change Escape (rows 4 ⊔ rows 2)
    simpa only [sup_comm] using escape24
  · change Escape (rows 4 ⊔ rows 3)
    simpa only [sup_comm] using escape34
  · exact (hij rfl).elim

theorem atom_le_joined (s : Finset (Fin 4)) (i : Fin 4) (hi : i ∈ s) : atoms i ≤ joined s :=
  (Finset.le_sup hi).trans le_sup_right

theorem joined_is_model_or_escape (s : Finset (Fin 4)) :
    (∃ i : Fin 5, joined s = rows i) ∨ Escape (joined s) := by
  classical
  by_cases hempty : s = ∅
  · exact Or.inl ⟨0, (congrArg joined hempty).trans joined_empty⟩
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  by_cases hone : s = {a}
  · left
    fin_cases a
    · exact ⟨1, (congrArg joined hone).trans (joined_singleton 0)⟩
    · exact ⟨2, (congrArg joined hone).trans (joined_singleton 1)⟩
    · exact ⟨3, (congrArg joined hone).trans (joined_singleton 2)⟩
    · exact ⟨4, (congrArg joined hone).trans (joined_singleton 3)⟩
  have hexists : ∃ b ∈ s, b ≠ a := by
    by_contra hn
    apply hone
    ext b
    constructor
    · intro hb
      have hba : b = a := by
        by_contra hne
        exact hn ⟨b, hb, hne⟩
      exact Finset.mem_singleton.mpr hba
    · intro hb
      rcases Finset.mem_singleton.mp hb with rfl
      exact ha
  obtain ⟨b, hb, hba⟩ := hexists
  right
  exact PermutationPrimePowerSeedEscape.mono 2 8 _ _
    (sup_le (atom_le_joined s a ha) (atom_le_joined s b hb)) (escape_distinct a b hba.symm)

end SymmetricSubgroupAsymptotics.S8Seed5AtomRows
end
