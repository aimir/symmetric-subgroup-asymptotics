import SymmetricSubgroupAsymptotics.FiniteSeedAtomJoinRows
import SymmetricSubgroupAsymptotics.S8Seed29LowConjugacy
import SymmetricSubgroupAsymptotics.S8Seed29LowJoin4_7
import SymmetricSubgroupAsymptotics.S8Seed29LowJoin5_7
import SymmetricSubgroupAsymptotics.S8Seed29LowJoin1_4
import SymmetricSubgroupAsymptotics.S8Seed29LowNormalizer5
import Mathlib.Data.Fintype.Powerset

/-! The low family is the set of joins of three actual atom subgroups.
Three ordinary-word join equations identify all its literal models.
Join closure follows from finite-set union; no64-case table is used. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed29AtomRows
open S8Seed29LeftCosets S8Seed29LowModels

def atoms : Fin 3 → Subgroup Ambient := ![rows 4, rows 5, rows 7]

def joined (s : Finset (Fin 3)) : Subgroup Ambient :=
  FiniteSeedAtomJoinRows.rows H atoms s

theorem seed_le_atom (i : Fin 3) : H ≤ atoms i := by
  fin_cases i
  · exact S8Seed29LowConjugacy.seed_le 4
  · exact S8Seed29LowConjugacy.seed_le 5
  · exact S8Seed29LowConjugacy.seed_le 7

theorem joined_empty : joined ∅ = rows 0 :=
  (FiniteSeedAtomJoinRows.empty H atoms).trans rows_zero.symm

theorem joined_singleton (i : Fin 3) : joined {i} = atoms i := by
  simp only [joined, FiniteSeedAtomJoinRows.rows, Finset.sup_singleton]
  exact sup_eq_right.mpr (seed_le_atom i)

theorem joined_union (s t : Finset (Fin 3)) : joined s ⊔ joined t = joined (s ∪ t) :=
  FiniteSeedAtomJoinRows.union H atoms s t

theorem join4_5 : rows 4 ⊔ rows 5 = rows 6 := by
  have h := congrArg (fun W : Subgroup Ambient =>
    MulAut.conj S8Seed29NormalizerRoots.normalizer • W) S8Seed29LowJoin5_7.exact_eq
  dsimp only at h
  rw [Subgroup.smul_sup, S8Seed29LowNormalizer5.exact_eq,
    S8Seed29LowConjugacy.conjugates_row7, S8Seed29LowConjugacy.conjugates_row1] at h
  simpa only [sup_comm] using h

theorem joined_pair01 : joined {0, 1} = rows 6 := by
  have h := joined_union {0} {1}
  rw [Finset.singleton_union, joined_singleton, joined_singleton] at h
  change rows 4 ⊔ rows 5 = joined {0, 1} at h
  exact h.symm.trans join4_5

theorem joined_pair02 : joined {0, 2} = rows 3 := by
  have h := joined_union {0} {2}
  rw [Finset.singleton_union, joined_singleton, joined_singleton] at h
  change rows 4 ⊔ rows 7 = joined {0, 2} at h
  exact h.symm.trans S8Seed29LowJoin4_7.exact_eq

theorem joined_pair12 : joined {1, 2} = rows 1 := by
  have h := joined_union {1} {2}
  rw [Finset.singleton_union, joined_singleton, joined_singleton] at h
  change rows 5 ⊔ rows 7 = joined {1, 2} at h
  exact h.symm.trans S8Seed29LowJoin5_7.exact_eq

theorem joined_triple : joined {0, 1, 2} = rows 2 := by
  have h := joined_union {1, 2} {0}
  have hset : ({1, 2} ∪ {0} : Finset (Fin 3)) = {0, 1, 2} := by decide +kernel
  rw [hset, joined_pair12, joined_singleton] at h
  exact h.symm.trans S8Seed29LowJoin1_4.exact_eq

def atomPermutation : Fin 3 → Fin 3 := ![2, 1, 0]

theorem conjugates_atoms (i : Fin 3) : MulAut.conj S8Seed29NormalizerRoots.normalizer •
    atoms i = atoms (atomPermutation i) := by
  fin_cases i
  · exact S8Seed29LowConjugacy.conjugates_row4
  · exact S8Seed29LowNormalizer5.exact_eq
  · exact S8Seed29LowConjugacy.conjugates_row7

theorem conjugates_joined (s : Finset (Fin 3)) :
    MulAut.conj S8Seed29NormalizerRoots.normalizer • joined s =
      joined (s.image atomPermutation) :=
  FiniteSeedAtomJoinRows.conjugated H atoms S8Seed29NormalizerRoots.normalizer
    atomPermutation S8Seed29NormalizerRoots.normalizes_seed conjugates_atoms s

/-- Every literal low model has an actual finite-atom join description. -/
theorem model_is_joined (i : Fin 8) : ∃ s : Finset (Fin 3), rows i = joined s := by
  fin_cases i
  · exact ⟨∅, joined_empty.symm⟩
  · exact ⟨{1, 2}, joined_pair12.symm⟩
  · exact ⟨{0, 1, 2}, joined_triple.symm⟩
  · exact ⟨{0, 2}, joined_pair02.symm⟩
  · exact ⟨{0}, (joined_singleton 0).symm⟩
  · exact ⟨{1}, (joined_singleton 1).symm⟩
  · exact ⟨{0, 1}, joined_pair01.symm⟩
  · exact ⟨{2}, (joined_singleton 2).symm⟩

private theorem finset_ext_three (s t : Finset (Fin 3))
    (h0 : (0 ∈ s ↔ 0 ∈ t)) (h1 : (1 ∈ s ↔ 1 ∈ t))
    (h2 : (2 ∈ s ↔ 2 ∈ t)) : s = t := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The arbitrary finite joins introduce no additional literal action. -/
theorem joined_is_model (s : Finset (Fin 3)) : ∃ i : Fin 8, joined s = rows i := by
  by_cases h0 : (0 : Fin 3) ∈ s
  · by_cases h1 : (1 : Fin 3) ∈ s
    · by_cases h2 : (2 : Fin 3) ∈ s
      · have hs : s = {0, 1, 2} := finset_ext_three _ _ (by simp [h0])
          (by simp [h1]) (by simp [h2])
        exact ⟨2, (congrArg joined hs).trans joined_triple⟩
      · have hs : s = {0, 1} := finset_ext_three _ _ (by simp [h0])
          (by simp [h1]) (by simp [h2])
        exact ⟨6, (congrArg joined hs).trans joined_pair01⟩
    · by_cases h2 : (2 : Fin 3) ∈ s
      · have hs : s = {0, 2} := finset_ext_three _ _ (by simp [h0])
          (by simp [h1]) (by simp [h2])
        exact ⟨3, (congrArg joined hs).trans joined_pair02⟩
      · have hs : s = {0} := finset_ext_three _ _ (by simp [h0])
          (by simp [h1]) (by simp [h2])
        exact ⟨4, (congrArg joined hs).trans (joined_singleton 0)⟩
  · by_cases h1 : (1 : Fin 3) ∈ s
    · by_cases h2 : (2 : Fin 3) ∈ s
      · have hs : s = {1, 2} := finset_ext_three _ _ (by simp [h0])
          (by simp [h1]) (by simp [h2])
        exact ⟨1, (congrArg joined hs).trans joined_pair12⟩
      · have hs : s = {1} := finset_ext_three _ _ (by simp [h0])
          (by simp [h1]) (by simp [h2])
        exact ⟨5, (congrArg joined hs).trans (joined_singleton 1)⟩
    · by_cases h2 : (2 : Fin 3) ∈ s
      · have hs : s = {2} := finset_ext_three _ _ (by simp [h0])
          (by simp [h1]) (by simp [h2])
        exact ⟨7, (congrArg joined hs).trans (joined_singleton 2)⟩
      · have hs : s = ∅ := finset_ext_three _ _ (by simp [h0])
          (by simp [h1]) (by simp [h2])
        exact ⟨0, (congrArg joined hs).trans joined_empty⟩

end SymmetricSubgroupAsymptotics.S8Seed29AtomRows
end
