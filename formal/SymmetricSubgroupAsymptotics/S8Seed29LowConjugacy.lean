import SymmetricSubgroupAsymptotics.S8Seed29LowModels

/-! Structural facts about the actual eight low candidates. Normalizer
images use the displayed point permutation; seed containment is obtained
from the original generators, not from a numerical order comparison. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.S8Seed29LowConjugacy
open S8Seed29LeftCosets S8Seed29LowModels

theorem conjugates_row1 : MulAut.conj S8Seed29NormalizerRoots.normalizer • rows 1 = rows 6 := by
  change (Subgroup.closure (Set.range (rootGenerators 3))).map
      (MulAut.conj S8Seed29NormalizerRoots.normalizer).toMonoidHom =
    Subgroup.closure (Set.range
      (fun j => (MulAut.conj S8Seed29NormalizerRoots.normalizer) (rootGenerators 3 j)))
  rw [MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨rootGenerators 3 j, ⟨j, rfl⟩, rfl⟩

theorem conjugates_row4 : MulAut.conj S8Seed29NormalizerRoots.normalizer • rows 4 = rows 7 := by
  change (Subgroup.closure (Set.range (rootGenerators 17))).map
      (MulAut.conj S8Seed29NormalizerRoots.normalizer).toMonoidHom =
    Subgroup.closure (Set.range
      (fun j => (MulAut.conj S8Seed29NormalizerRoots.normalizer) (rootGenerators 17 j)))
  rw [MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨rootGenerators 17 j, ⟨j, rfl⟩, rfl⟩

theorem conjugates_row6 : MulAut.conj S8Seed29NormalizerRoots.normalizer • rows 6 = rows 1 := by
  rw [← conjugates_row1, ← mul_smul, ← map_mul, normalizer_sq, map_one, one_smul]

theorem conjugates_row7 : MulAut.conj S8Seed29NormalizerRoots.normalizer • rows 7 = rows 4 := by
  rw [← conjugates_row4, ← mul_smul, ← map_mul, normalizer_sq, map_one, one_smul]

theorem root_contains (k : Fin 32) : H ≤ Subgroup.closure (Set.range (rootGenerators k)) := by
  rw [root_closure]
  exact le_sup_left

theorem seed_le (i : Fin 8) : H ≤ rows i := by
  fin_cases i
  · exact root_contains 0
  · exact root_contains 3
  · exact root_contains 4
  · exact root_contains 10
  · exact root_contains 17
  · exact root_contains 30
  · have h : MulAut.conj S8Seed29NormalizerRoots.normalizer • H ≤
        MulAut.conj S8Seed29NormalizerRoots.normalizer • rows 1 := by
      change H.map (MulAut.conj S8Seed29NormalizerRoots.normalizer).toMonoidHom ≤
        (rows 1).map (MulAut.conj S8Seed29NormalizerRoots.normalizer).toMonoidHom
      exact Subgroup.map_mono (root_contains 3)
    rwa [S8Seed29NormalizerRoots.normalizes_seed, conjugates_row1] at h
  · have h : MulAut.conj S8Seed29NormalizerRoots.normalizer • H ≤
        MulAut.conj S8Seed29NormalizerRoots.normalizer • rows 4 := by
      change H.map (MulAut.conj S8Seed29NormalizerRoots.normalizer).toMonoidHom ≤
        (rows 4).map (MulAut.conj S8Seed29NormalizerRoots.normalizer).toMonoidHom
      exact Subgroup.map_mono (root_contains 17)
    rwa [S8Seed29NormalizerRoots.normalizes_seed, conjugates_row4] at h

end SymmetricSubgroupAsymptotics.S8Seed29LowConjugacy

end
