import SymmetricSubgroupAsymptotics.S8Seed5NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Actual displayed low rows. Identity padding only gives a common word
alphabet; every original-seed inclusion is certified by ordinary words. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed5LowModels
open S8Seed5LeftCosets

private def permutation0_0 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation0_1 : Ambient where
  toFun := ![6, 5, 4, 1, 0, 7, 2, 3]
  invFun := ![4, 3, 6, 7, 2, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation0_2 : Ambient where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation1_0 : Ambient where
  toFun := ![2, 6, 0, 7, 5, 1, 3, 4]
  invFun := ![2, 5, 0, 6, 7, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation1_1 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation1_2 : Ambient where
  toFun := ![6, 5, 4, 1, 0, 7, 2, 3]
  invFun := ![4, 3, 6, 7, 2, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation2_0 : Ambient where
  toFun := ![6, 7, 4, 2, 5, 0, 3, 1]
  invFun := ![5, 7, 3, 6, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation2_1 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation2_2 : Ambient where
  toFun := ![6, 5, 4, 1, 0, 7, 2, 3]
  invFun := ![4, 3, 6, 7, 2, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation3_0 : Ambient where
  toFun := ![2, 4, 0, 1, 5, 7, 3, 6]
  invFun := ![2, 3, 0, 6, 1, 4, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation3_1 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation3_2 : Ambient where
  toFun := ![6, 5, 4, 1, 0, 7, 2, 3]
  invFun := ![4, 3, 6, 7, 2, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation4_0 : Ambient where
  toFun := ![1, 3, 7, 2, 6, 0, 4, 5]
  invFun := ![5, 0, 3, 1, 6, 7, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation4_1 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation4_2 : Ambient where
  toFun := ![4, 3, 6, 7, 2, 1, 0, 5]
  invFun := ![6, 5, 4, 1, 0, 7, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (i : Fin 5) : Fin 3 → Ambient :=
  (![![permutation0_0, permutation0_1, permutation0_2], ![permutation1_0, permutation1_1, permutation1_2], ![permutation2_0, permutation2_1, permutation2_2], ![permutation3_0, permutation3_1, permutation3_2], ![permutation4_0, permutation4_1, permutation4_2]] : Fin 5 → Fin 3 → Ambient) i

def rows (i : Fin 5) : Subgroup Ambient := Subgroup.closure (Set.range (generators i))

def seedWords (i : Fin 5) : Fin 2 → FiniteGeneratorWord (Fin 3) :=
  (![![(.generator 0), (.generator 1)], ![(.generator 1), (.generator 2)], ![(.generator 1), (.generator 2)], ![(.generator 1), (.generator 2)], ![(.generator 1), (.inv (.generator 2))]] : Fin 5 → Fin 2 → FiniteGeneratorWord (Fin 3)) i

set_option maxHeartbeats 1000000 in
theorem seed_equation (i : Fin 5) (j : Fin 2) :
    (seedWords i j).eval (generators i) = BinaryMenuCayley8T5.generators j := by
  apply Equiv.ext
  intro x
  revert i j x
  decide +kernel

theorem seed_le (i : Fin 5) : H ≤ rows i := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨j, rfl⟩
  rw [←seed_equation i j]
  exact (seedWords i j).eval_mem_closure (generators i)

def zeroCertificate : FiniteGeneratorEquivWordCertificate (MulEquiv.refl Ambient)
    BinaryMenuCayley8T5.generators (generators 0) where
  forward := {
    words := ![(.generator 0), (.generator 1)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 0), (.generator 1), .one]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem rows_zero : rows 0 = H := by
  have h := zeroCertificate.map_closure_eq
  change H.map (MonoidHom.id Ambient) = rows 0 at h
  rw [Subgroup.map_id] at h
  exact h.symm

end SymmetricSubgroupAsymptotics.S8Seed5LowModels
end
