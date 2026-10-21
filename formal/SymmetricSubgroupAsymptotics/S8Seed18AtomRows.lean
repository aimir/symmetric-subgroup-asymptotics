import SymmetricSubgroupAsymptotics.FiniteSeedAtomJoinRows
import SymmetricSubgroupAsymptotics.S8Seed18LowJoin2_3
import SymmetricSubgroupAsymptotics.S8Seed18LowNormalizer2
import SymmetricSubgroupAsymptotics.S8Seed18LowNormalizer3
import Mathlib.Data.Fintype.Powerset

/-! The low family is the finite joins of two actual atom subgroups.
One ordinary-word join identifies their top; join closure is finite-set
union, and the selected normalizer fixes both actual atoms. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed18AtomRows
open S8Seed18LeftCosets S8Seed18LowModels

def atoms : Fin 2 → Subgroup Ambient := ![rows 2, rows 3]

def joined (s : Finset (Fin 2)) : Subgroup Ambient :=
  FiniteSeedAtomJoinRows.rows H atoms s

theorem seed_le_atom (i : Fin 2) : H ≤ atoms i := by
  fin_cases i
  · exact S8Seed18LowModels.seed_le 2
  · exact S8Seed18LowModels.seed_le 3

theorem joined_empty : joined ∅ = rows 0 :=
  (FiniteSeedAtomJoinRows.empty H atoms).trans rows_zero.symm

theorem joined_singleton (i : Fin 2) : joined {i} = atoms i := by
  simp only [joined, FiniteSeedAtomJoinRows.rows, Finset.sup_singleton]
  exact sup_eq_right.mpr (seed_le_atom i)

theorem joined_union (s t : Finset (Fin 2)) : joined s ⊔ joined t = joined (s ∪ t) :=
  FiniteSeedAtomJoinRows.union H atoms s t

theorem joined_pair : joined {0, 1} = rows 1 := by
  have h := joined_union {0} {1}
  rw [Finset.singleton_union, joined_singleton, joined_singleton] at h
  change rows 2 ⊔ rows 3 = joined {0, 1} at h
  exact h.symm.trans S8Seed18LowJoin2_3.exact_eq

theorem conjugates_atoms (i : Fin 2) :
    MulAut.conj S8Seed18NormalizerRoots.normalizer • atoms i = atoms i := by
  fin_cases i
  · exact S8Seed18LowNormalizer2.exact_eq
  · exact S8Seed18LowNormalizer3.exact_eq

theorem conjugates_joined (s : Finset (Fin 2)) :
    MulAut.conj S8Seed18NormalizerRoots.normalizer • joined s = joined s := by
  have h := FiniteSeedAtomJoinRows.conjugated H atoms S8Seed18NormalizerRoots.normalizer
    (fun i => i) S8Seed18NormalizerRoots.normalizes_seed conjugates_atoms s
  simpa only [joined, Finset.image_id'] using h

theorem model_is_joined (i : Fin 4) : ∃ s : Finset (Fin 2), rows i = joined s := by
  fin_cases i
  · exact ⟨∅, joined_empty.symm⟩
  · exact ⟨{0, 1}, joined_pair.symm⟩
  · exact ⟨{0}, (joined_singleton 0).symm⟩
  · exact ⟨{1}, (joined_singleton 1).symm⟩

private theorem finset_ext_two (s t : Finset (Fin 2))
    (h0 : (0 ∈ s ↔ 0 ∈ t)) (h1 : (1 ∈ s ↔ 1 ∈ t)) : s = t := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem joined_is_model (s : Finset (Fin 2)) : ∃ i : Fin 4, joined s = rows i := by
  by_cases h0 : (0 : Fin 2) ∈ s
  · by_cases h1 : (1 : Fin 2) ∈ s
    · have hs : s = {0, 1} := finset_ext_two _ _ (by simp [h0]) (by simp [h1])
      exact ⟨1, (congrArg joined hs).trans joined_pair⟩
    · have hs : s = {0} := finset_ext_two _ _ (by simp [h0]) (by simp [h1])
      exact ⟨2, (congrArg joined hs).trans (joined_singleton 0)⟩
  · by_cases h1 : (1 : Fin 2) ∈ s
    · have hs : s = {1} := finset_ext_two _ _ (by simp [h0]) (by simp [h1])
      exact ⟨3, (congrArg joined hs).trans (joined_singleton 1)⟩
    · have hs : s = ∅ := finset_ext_two _ _ (by simp [h0]) (by simp [h1])
      exact ⟨0, (congrArg joined hs).trans joined_empty⟩

end SymmetricSubgroupAsymptotics.S8Seed18AtomRows
end
