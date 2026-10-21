import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Two literal ambient generators for later selected S8 coset covers.
The adjacent transpositions are explicit conjugates of one transposition
by powers of the actual eight-cycle. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SymmetricEightTwoGenerators

abbrev Ambient := Equiv.Perm (Fin 8)

def rotation : Ambient where
  toFun := ![1, 2, 3, 4, 5, 6, 7, 0]
  invFun := ![7, 0, 1, 2, 3, 4, 5, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Ambient := ![rotation, Equiv.swap 0 1]

theorem rotation_conjugate_swap (i : Fin 7) :
    (generators 0) ^ i.val * generators 1 * ((generators 0) ^ i.val)⁻¹ =
      Equiv.swap i.castSucc i.succ := by
  fin_cases i <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

theorem generators_full : Subgroup.closure (Set.range generators) = ⊤ := by
  have hfull : Subgroup.closure (Set.range
      (fun i : Fin 7 => Equiv.swap i.castSucc i.succ)) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top
      (Equiv.Perm.mclosure_swap_castSucc_succ 7)
  apply top_unique
  rw [← hfull]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change Equiv.swap i.castSucc i.succ ∈ Subgroup.closure (Set.range generators)
  rw [← rotation_conjugate_swap i]
  let S := Subgroup.closure (Set.range generators)
  have hrotation : generators 0 ∈ S := Subgroup.subset_closure (Set.mem_range_self 0)
  have hswap : generators 1 ∈ S := Subgroup.subset_closure (Set.mem_range_self 1)
  exact S.mul_mem (S.mul_mem (S.pow_mem hrotation _) hswap)
    (S.inv_mem (S.pow_mem hrotation _))

end SymmetricSubgroupAsymptotics.SymmetricEightTwoGenerators

end
