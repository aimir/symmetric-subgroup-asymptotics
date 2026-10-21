import SymmetricSubgroupAsymptotics.S8Seed4NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Actual displayed low rows. Identity padding only gives a common word
alphabet; every original-seed inclusion is certified by ordinary words. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed4LowModels
open S8Seed4LeftCosets

private def permutation0_0 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation0_1 : Ambient where
  toFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  invFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation0_2 : Ambient where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation1_0 : Ambient where
  toFun := ![1, 2, 0, 3, 4, 7, 5, 6]
  invFun := ![2, 0, 1, 3, 4, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation1_1 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation1_2 : Ambient where
  toFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  invFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation2_0 : Ambient where
  toFun := ![7, 5, 6, 4, 3, 1, 2, 0]
  invFun := ![7, 5, 6, 4, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation2_1 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation2_2 : Ambient where
  toFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  invFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation3_0 : Ambient where
  toFun := ![7, 4, 6, 5, 1, 3, 2, 0]
  invFun := ![7, 4, 6, 5, 1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation3_1 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation3_2 : Ambient where
  toFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  invFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation4_0 : Ambient where
  toFun := ![7, 6, 3, 2, 5, 4, 1, 0]
  invFun := ![7, 6, 3, 2, 5, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation4_1 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation4_2 : Ambient where
  toFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  invFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation5_0 : Ambient where
  toFun := ![5, 3, 6, 7, 4, 2, 1, 0]
  invFun := ![7, 6, 5, 1, 4, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation5_1 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation5_2 : Ambient where
  toFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  invFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation6_0 : Ambient where
  toFun := ![6, 3, 7, 1, 5, 4, 0, 2]
  invFun := ![6, 3, 7, 1, 5, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation6_1 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation6_2 : Ambient where
  toFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  invFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation7_0 : Ambient where
  toFun := ![0, 3, 1, 2, 5, 6, 4, 7]
  invFun := ![0, 2, 3, 1, 6, 4, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation7_1 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation7_2 : Ambient where
  toFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  invFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation8_0 : Ambient where
  toFun := ![1, 0, 5, 4, 3, 2, 7, 6]
  invFun := ![1, 0, 5, 4, 3, 2, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation8_1 : Ambient where
  toFun := ![1, 2, 7, 4, 5, 6, 3, 0]
  invFun := ![7, 0, 1, 6, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def permutation8_2 : Ambient where
  toFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  invFun := ![5, 4, 3, 2, 1, 0, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (i : Fin 9) : Fin 3 → Ambient :=
  (![![permutation0_0, permutation0_1, permutation0_2], ![permutation1_0, permutation1_1, permutation1_2], ![permutation2_0, permutation2_1, permutation2_2], ![permutation3_0, permutation3_1, permutation3_2], ![permutation4_0, permutation4_1, permutation4_2], ![permutation5_0, permutation5_1, permutation5_2], ![permutation6_0, permutation6_1, permutation6_2], ![permutation7_0, permutation7_1, permutation7_2], ![permutation8_0, permutation8_1, permutation8_2]] : Fin 9 → Fin 3 → Ambient) i

def rows (i : Fin 9) : Subgroup Ambient := Subgroup.closure (Set.range (generators i))

def seedWords (i : Fin 9) : Fin 2 → FiniteGeneratorWord (Fin 3) :=
  (![![(.generator 0), (.generator 1)], ![(.generator 1), (.generator 2)], ![(.generator 1), (.generator 2)], ![(.generator 1), (.generator 2)], ![(.generator 1), (.generator 2)], ![(.generator 1), (.generator 2)], ![(.generator 1), (.generator 2)], ![(.generator 1), (.generator 2)], ![(.generator 1), (.generator 2)]] : Fin 9 → Fin 2 → FiniteGeneratorWord (Fin 3)) i

set_option maxHeartbeats 1000000 in
theorem seed_equation (i : Fin 9) (j : Fin 2) :
    (seedWords i j).eval (generators i) = BinaryMenuCayley8T4.generators j := by
  apply Equiv.ext
  intro x
  revert i j x
  decide +kernel

theorem seed_le (i : Fin 9) : H ≤ rows i := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨j, rfl⟩
  rw [←seed_equation i j]
  exact (seedWords i j).eval_mem_closure (generators i)

def zeroCertificate : FiniteGeneratorEquivWordCertificate (MulEquiv.refl Ambient)
    BinaryMenuCayley8T4.generators (generators 0) where
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

end SymmetricSubgroupAsymptotics.S8Seed4LowModels
end
