import SymmetricSubgroupAsymptotics.S8Seed9NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteSubgroupJoinWords
import Mathlib.Tactic.FinCases

/-! The original seed, two literal low roots and both actual normalizer conjugates. No
normalizer fixation or overgroup coverage is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed9LowModels
open S8Seed9LeftCosets

def rootGenerators (k : Fin 164) : Fin 5 → Ambient :=
  Matrix.vecCons (representatives (S8Seed9NormalizerRoots.roots k)) BinaryMenuCayley8T9.generators

def generators : Fin 5 → Fin 5 → Ambient :=
  ![rootGenerators 0,rootGenerators 8,rootGenerators 37,
    fun j => (MulAut.conj S8Seed9NormalizerRoots.normalizer) (rootGenerators 8 j),
    fun j => (MulAut.conj S8Seed9NormalizerRoots.normalizer) (rootGenerators 37 j)]

def rows (i : Fin 5) : Subgroup Ambient := Subgroup.closure (Set.range (generators i))

theorem root_closure (k : Fin 164) : Subgroup.closure (Set.range (rootGenerators k)) =
    H ⊔ Subgroup.closure {representatives (S8Seed9NormalizerRoots.roots k)} := by
  simp only [rootGenerators,Matrix.range_cons,Subgroup.closure_union,sup_comm]

theorem rows_zero : rows 0 = H := by
  change Subgroup.closure (Set.range (rootGenerators 0)) = H
  rw [root_closure,S8Seed9NormalizerRoots.root_zero_eq_seed]

theorem seed_le_root (k : Fin 164) : H ≤ Subgroup.closure (Set.range (rootGenerators k)) := by
  rw [root_closure]
  exact le_sup_left

theorem normalizer_one_definitional :
    MulAut.conj S8Seed9NormalizerRoots.normalizer • rows 1 = rows 3 := by
  change (Subgroup.closure (Set.range (rootGenerators 8))).map
      (MulAut.conj S8Seed9NormalizerRoots.normalizer).toMonoidHom =
    Subgroup.closure (Set.range
      (fun j => (MulAut.conj S8Seed9NormalizerRoots.normalizer) (rootGenerators 8 j)))
  rw [MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨y,⟨j,rfl⟩,rfl⟩
    exact ⟨j,rfl⟩
  · rintro ⟨j,rfl⟩
    exact ⟨rootGenerators 8 j,⟨j,rfl⟩,rfl⟩

theorem normalizer_two_definitional :
    MulAut.conj S8Seed9NormalizerRoots.normalizer • rows 2 = rows 4 := by
  change (Subgroup.closure (Set.range (rootGenerators 37))).map
      (MulAut.conj S8Seed9NormalizerRoots.normalizer).toMonoidHom =
    Subgroup.closure (Set.range
      (fun j => (MulAut.conj S8Seed9NormalizerRoots.normalizer) (rootGenerators 37 j)))
  rw [MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨y,⟨j,rfl⟩,rfl⟩
    exact ⟨j,rfl⟩
  · rintro ⟨j,rfl⟩
    exact ⟨rootGenerators 37 j,⟨j,rfl⟩,rfl⟩

theorem seed_le (i : Fin 5) : H ≤ rows i := by
  fin_cases i
  · exact seed_le_root 0
  · exact seed_le_root 8
  · exact seed_le_root 37
  · have h : H.map (MulAut.conj S8Seed9NormalizerRoots.normalizer).toMonoidHom ≤
        (rows 1).map (MulAut.conj S8Seed9NormalizerRoots.normalizer).toMonoidHom :=
      Subgroup.map_mono (seed_le_root 8)
    change MulAut.conj S8Seed9NormalizerRoots.normalizer • H ≤
      MulAut.conj S8Seed9NormalizerRoots.normalizer • rows 1 at h
    rw [S8Seed9NormalizerRoots.normalizes_seed,normalizer_one_definitional] at h
    exact h
  · have h : H.map (MulAut.conj S8Seed9NormalizerRoots.normalizer).toMonoidHom ≤
        (rows 2).map (MulAut.conj S8Seed9NormalizerRoots.normalizer).toMonoidHom :=
      Subgroup.map_mono (seed_le_root 37)
    change MulAut.conj S8Seed9NormalizerRoots.normalizer • H ≤
      MulAut.conj S8Seed9NormalizerRoots.normalizer • rows 2 at h
    rw [S8Seed9NormalizerRoots.normalizes_seed,normalizer_two_definitional] at h
    exact h

end SymmetricSubgroupAsymptotics.S8Seed9LowModels
end
