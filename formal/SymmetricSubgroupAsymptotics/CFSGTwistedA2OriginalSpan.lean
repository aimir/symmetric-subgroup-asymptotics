import SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratedInvariantSpan
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! The original rational A2 quotient is spanned by its literal eight
Chevalley vectors. The proof uses defining source relations and Lie
generation, not injectivity of a natural matrix realization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations

def vectors : Fin 8 → L := ![H 0, H 1, E 0, E 1, P, F 0, F 1, N]
def eightSpan : Submodule ℚ L := Submodule.span ℚ (Set.range vectors)

theorem vector_mem (i : Fin 8) : vectors i ∈ eightSpan := Submodule.subset_span ⟨i, rfl⟩
theorem H_mem (i : Fin 2) : H i ∈ eightSpan := by
  fin_cases i
  · exact vector_mem 0
  · exact vector_mem 1
theorem E_mem (i : Fin 2) : E i ∈ eightSpan := by
  fin_cases i
  · exact vector_mem 2
  · exact vector_mem 3
theorem P_mem : P ∈ eightSpan := vector_mem 4
theorem F_mem (i : Fin 2) : F i ∈ eightSpan := by
  fin_cases i
  · exact vector_mem 5
  · exact vector_mem 6
theorem N_mem : N ∈ eightSpan := vector_mem 7

theorem E_H_mem (i j : Fin 2) : ⁅E i, H j⁆ ∈ eightSpan := by
  rw [← lie_skew (E i) (H j), H_E]
  exact eightSpan.neg_mem (eightSpan.toAddSubgroup.zsmul_mem (E_mem i) (A j i))
theorem F_H_mem (i j : Fin 2) : ⁅F i, H j⁆ ∈ eightSpan := by
  rw [← lie_skew (F i) (H j), H_F, neg_neg]
  exact eightSpan.toAddSubgroup.zsmul_mem (F_mem i) (A j i)
theorem E_E_mem (i j : Fin 2) : ⁅E i, E j⁆ ∈ eightSpan := by
  fin_cases i <;> fin_cases j
  · rw [lie_self]; exact eightSpan.zero_mem
  · exact P_mem
  · change ⁅E 1, E 0⁆ ∈ eightSpan
    rw [← lie_skew (E 1) (E 0)]; exact eightSpan.neg_mem P_mem
  · rw [lie_self]; exact eightSpan.zero_mem
theorem F_F_mem (i j : Fin 2) : ⁅F i, F j⁆ ∈ eightSpan := by
  fin_cases i <;> fin_cases j
  · rw [lie_self]; exact eightSpan.zero_mem
  · change ⁅F 0, F 1⁆ ∈ eightSpan
    rw [← lie_skew (F 0) (F 1)]; exact eightSpan.neg_mem N_mem
  · exact N_mem
  · rw [lie_self]; exact eightSpan.zero_mem
theorem E_F_mem (i j : Fin 2) : ⁅E i, F j⁆ ∈ eightSpan := by
  by_cases h : i = j
  · subst j; rw [E_F_same]; exact H_mem i
  · rw [E_F_ne i j h]; exact eightSpan.zero_mem
theorem F_E_mem (i j : Fin 2) : ⁅F i, E j⁆ ∈ eightSpan := by
  by_cases h : i = j
  · subst j; rw [F_E_same]; exact eightSpan.neg_mem (H_mem i)
  · rw [F_E_ne i j h]; exact eightSpan.zero_mem

theorem E_vector_mem (i : Fin 2) (j : Fin 8) : ⁅E i, vectors j⁆ ∈ eightSpan := by
  fin_cases j
  · exact E_H_mem i 0
  · exact E_H_mem i 1
  · exact E_E_mem i 0
  · exact E_E_mem i 1
  · change ⁅E i, P⁆ ∈ eightSpan
    rw [E_P]; exact eightSpan.zero_mem
  · exact E_F_mem i 0
  · exact E_F_mem i 1
  · change ⁅E i, N⁆ ∈ eightSpan
    fin_cases i
    · change ⁅E 0, N⁆ ∈ eightSpan
      rw [E0_N]; exact eightSpan.neg_mem (F_mem 1)
    · change ⁅E 1, N⁆ ∈ eightSpan
      rw [E1_N]; exact F_mem 0

theorem F_vector_mem (i : Fin 2) (j : Fin 8) : ⁅F i, vectors j⁆ ∈ eightSpan := by
  fin_cases j
  · exact F_H_mem i 0
  · exact F_H_mem i 1
  · exact F_E_mem i 0
  · exact F_E_mem i 1
  · change ⁅F i, P⁆ ∈ eightSpan
    fin_cases i
    · change ⁅F 0, P⁆ ∈ eightSpan
      rw [F0_P]; exact E_mem 1
    · change ⁅F 1, P⁆ ∈ eightSpan
      rw [F1_P]; exact eightSpan.neg_mem (E_mem 0)
  · exact F_F_mem i 0
  · exact F_F_mem i 1
  · change ⁅F i, N⁆ ∈ eightSpan
    rw [F_N]; exact eightSpan.zero_mem

theorem E_preserves_span (i : Fin 2) (x : L) (hx : x ∈ eightSpan) : ⁅E i, x⁆ ∈ eightSpan := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact E_vector_mem i j
  | zero => rw [lie_zero]; exact eightSpan.zero_mem
  | add x y _ _ hx hy => rw [lie_add]; exact eightSpan.add_mem hx hy
  | smul a x _ hx => rw [lie_smul]; exact eightSpan.smul_mem a hx

theorem F_preserves_span (i : Fin 2) (x : L) (hx : x ∈ eightSpan) : ⁅F i, x⁆ ∈ eightSpan := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact F_vector_mem i j
  | zero => rw [lie_zero]; exact eightSpan.zero_mem
  | add x y _ _ hx hy => rw [lie_add]; exact eightSpan.add_mem hx hy
  | smul a x _ hx => rw [lie_smul]; exact eightSpan.smul_mem a hx

theorem eightSpan_eq_top : eightSpan = ⊤ :=
  CFSGSerreGeneratedInvariantSpan.eq_top_of_EF_stable A eightSpan
    E_mem F_mem E_preserves_span F_preserves_span

def rationalCombination : (Fin 8 → ℚ) →ₗ[ℚ] L := Fintype.linearCombination ℚ vectors

theorem rationalCombination_surjective : Function.Surjective rationalCombination := by
  apply LinearMap.range_eq_top.mp
  exact (Fintype.range_linearCombination ℚ vectors).trans eightSpan_eq_top

end SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
