import SymmetricSubgroupAsymptotics.BinaryHeisenberg
import Mathlib.GroupTheory.Abelianization.Defs

/-! Intrinsic structure of the actual binary Heisenberg group on eight points.
The scalar and fixed-commutator checks use literal coordinates, without
action tables or normal-subgroup enumeration. -/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics.RDTDegreeEightE8Structure

abbrev E8 := BinaryHeisenberg 2

def z : E8 := ⟨0, 0, 1⟩

private theorem kernel_elements (g : E8) :
    g ∈ (BinaryHeisenberg.quotient 2).ker ↔ g = 1 ∨ g = z := by
  rw [BinaryHeisenberg.mem_quotient_ker]
  constructor
  · rintro ⟨ha,hb⟩
    have hc : g.c = 0 ∨ g.c = 1 :=
      (by decide +kernel : ∀ c : ZMod 2, c = 0 ∨ c = 1) g.c
    rcases hc with hc | hc
    · left
      exact BinaryHeisenberg.ext ha hb hc
    · right
      exact BinaryHeisenberg.ext ha hb hc
  · rintro (rfl | rfl) <;> exact ⟨rfl,rfl⟩

private theorem z_commutator :
    ⁅(⟨![1,0], 0, 0⟩ : E8), (⟨0, ![1,0], 0⟩ : E8)⁆ = z := by
  apply BinaryHeisenberg.ext
  · ext i
    fin_cases i <;> decide +kernel
  · ext i
    fin_cases i <;> decide +kernel
  · decide +kernel

theorem commutator_eq_kernel :
    commutator E8 = (BinaryHeisenberg.quotient 2).ker := by
  apply le_antisymm
  · exact Abelianization.commutator_subset_ker (BinaryHeisenberg.quotient 2)
  · intro g hg
    rcases (kernel_elements g).mp hg with rfl | rfl
    · exact (commutator E8).one_mem
    · rw [← z_commutator]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
        (Subgroup.mem_top _)

theorem center_card : Nat.card (Subgroup.center E8) = 2 := by
  rw [BinaryHeisenberg.center_eq_quotient_ker]
  rw [← Nat.card_congr (BinaryHeisenberg.kernelChart 2).toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem commutator_card : Nat.card (commutator E8) = 2 := by
  rw [commutator_eq_kernel]
  rw [← Nat.card_congr (BinaryHeisenberg.kernelChart 2).toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- The actual derived subgroup is the actual centre. -/
theorem commutator_eq_center : commutator E8 = Subgroup.center E8 :=
  commutator_eq_kernel.trans (BinaryHeisenberg.center_eq_quotient_ker 2).symm

end SymmetricSubgroupAsymptotics.RDTDegreeEightE8Structure

end
