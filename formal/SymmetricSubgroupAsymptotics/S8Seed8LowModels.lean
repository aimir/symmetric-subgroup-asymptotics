import SymmetricSubgroupAsymptotics.S8Seed8NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteSubgroupJoinWords
import Mathlib.Tactic.FinCases

/-! The original seed, low97 and its actual normalizer conjugate. No
normalizer fixation or overgroup coverage is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed8LowModels
open S8Seed8LeftCosets

def rootGenerators (k : Fin 102) : Fin 3 → Ambient :=
  Matrix.vecCons (representatives (S8Seed8NormalizerRoots.roots k)) BinaryMenuCayley8T8.generators

def generators : Fin 3 → Fin 3 → Ambient :=
  ![rootGenerators 0,rootGenerators 97,
    fun j => (MulAut.conj S8Seed8NormalizerRoots.normalizer) (rootGenerators 97 j)]

def rows (i : Fin 3) : Subgroup Ambient := Subgroup.closure (Set.range (generators i))

theorem root_closure (k : Fin 102) : Subgroup.closure (Set.range (rootGenerators k)) =
    H ⊔ Subgroup.closure {representatives (S8Seed8NormalizerRoots.roots k)} := by
  simp only [rootGenerators,Matrix.range_cons,Subgroup.closure_union,sup_comm]

theorem rows_zero : rows 0 = H := by
  change Subgroup.closure (Set.range (rootGenerators 0)) = H
  rw [root_closure,S8Seed8NormalizerRoots.root_zero_eq_seed]

theorem seed_le_root (k : Fin 102) : H ≤ Subgroup.closure (Set.range (rootGenerators k)) := by
  rw [root_closure]
  exact le_sup_left

theorem normalizer_one_definitional :
    MulAut.conj S8Seed8NormalizerRoots.normalizer • rows 1 = rows 2 := by
  change (Subgroup.closure (Set.range (rootGenerators 97))).map
      (MulAut.conj S8Seed8NormalizerRoots.normalizer).toMonoidHom =
    Subgroup.closure (Set.range
      (fun j => (MulAut.conj S8Seed8NormalizerRoots.normalizer) (rootGenerators 97 j)))
  rw [MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨y,⟨j,rfl⟩,rfl⟩
    exact ⟨j,rfl⟩
  · rintro ⟨j,rfl⟩
    exact ⟨rootGenerators 97 j,⟨j,rfl⟩,rfl⟩

theorem seed_le (i : Fin 3) : H ≤ rows i := by
  fin_cases i
  · exact seed_le_root 0
  · exact seed_le_root 97
  · have h : H.map (MulAut.conj S8Seed8NormalizerRoots.normalizer).toMonoidHom ≤
        (rows 1).map (MulAut.conj S8Seed8NormalizerRoots.normalizer).toMonoidHom :=
      Subgroup.map_mono (seed_le_root 97)
    change MulAut.conj S8Seed8NormalizerRoots.normalizer • H ≤
      MulAut.conj S8Seed8NormalizerRoots.normalizer • rows 1 at h
    rw [S8Seed8NormalizerRoots.normalizes_seed,normalizer_one_definitional] at h
    exact h

end SymmetricSubgroupAsymptotics.S8Seed8LowModels
end
