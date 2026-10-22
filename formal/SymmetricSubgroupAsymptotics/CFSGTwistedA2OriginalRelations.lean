import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations
import Mathlib.Tactic.FinCases

/-! Actual rank-two Serre quotient relations for the eight-vector source
span. These identities are proved before any natural realization is
declared injective. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
abbrev A := CartanMatrix.A 2
abbrev L := RationalLie A
def E (i : Fin 2) : L := generator A (.E i)
def F (i : Fin 2) : L := generator A (.F i)
def H (i : Fin 2) : L := generator A (.H i)
def P : L := ⁅E 0, E 1⁆
def N : L := ⁅F 1, F 0⁆

theorem A01 : A 0 1 = -1 := by decide
theorem A10 : A 1 0 = -1 := by decide

theorem H_E (i j : Fin 2) : ⁅H i, E j⁆ = A i j • E j := generator_HE A i j
theorem H_F (i j : Fin 2) : ⁅H i, F j⁆ = -(A i j • F j) := generator_HF A i j
theorem E_F_same (i : Fin 2) : ⁅E i, F i⁆ = H i := generator_EF_same A i
theorem E_F_ne (i j : Fin 2) (h : i ≠ j) : ⁅E i, F j⁆ = 0 := generator_EF_ne A i j h
theorem F_E_same (i : Fin 2) : ⁅F i, E i⁆ = -H i := by rw [← lie_skew (F i) (E i), E_F_same]
theorem F_E_ne (i j : Fin 2) (h : i ≠ j) : ⁅F i, E j⁆ = 0 := by
  rw [← lie_skew (F i) (E j), E_F_ne j i (Ne.symm h), neg_zero]

theorem E_P (i : Fin 2) : ⁅E i, P⁆ = 0 := by
  fin_cases i
  · have h := generator_adE A (0 : Fin 2) 1
    rw [A01] at h
    change ⁅E 0, ⁅E 0, E 1⁆⁆ = 0 at h
    exact h
  · have h := generator_adE A (1 : Fin 2) 0
    rw [A10] at h
    change ⁅E 1, ⁅E 1, E 0⁆⁆ = 0 at h
    have hs : ⁅E 1, E 0⁆ = -P := (lie_skew _ _).symm
    rw [hs, lie_neg] at h
    exact neg_eq_zero.mp h

theorem F_N (i : Fin 2) : ⁅F i, N⁆ = 0 := by
  fin_cases i
  · have h := generator_adF A (0 : Fin 2) 1
    rw [A01] at h
    change ⁅F 0, ⁅F 0, F 1⁆⁆ = 0 at h
    have hs : ⁅F 0, F 1⁆ = -N := (lie_skew _ _).symm
    rw [hs, lie_neg] at h
    exact neg_eq_zero.mp h
  · have h := generator_adF A (1 : Fin 2) 0
    rw [A10] at h
    change ⁅F 1, ⁅F 1, F 0⁆⁆ = 0 at h
    exact h

theorem E0_N : ⁅E 0, N⁆ = -F 1 := by
  rw [N, leibniz_lie, E_F_ne 0 1 (by decide), E_F_same, zero_lie, zero_add,
    ← lie_skew (F 1) (H 0), H_F, A01]
  simp only [neg_one_zsmul, neg_neg]

theorem E1_N : ⁅E 1, N⁆ = F 0 := by
  rw [N, leibniz_lie, E_F_same, E_F_ne 1 0 (by decide), H_F, lie_zero, add_zero, A10]
  simp only [neg_one_zsmul, neg_neg]

theorem F0_P : ⁅F 0, P⁆ = E 1 := by
  rw [P, leibniz_lie, F_E_same, F_E_ne 0 1 (by decide), neg_lie, lie_zero,
    add_zero, H_E, A01]
  simp only [neg_one_zsmul, neg_neg]

theorem F1_P : ⁅F 1, P⁆ = -E 0 := by
  rw [P, leibniz_lie, F_E_ne 1 0 (by decide), F_E_same, zero_lie, zero_add,
    lie_neg, ← lie_skew (E 0) (H 1), neg_neg, H_E, A10]
  simp only [neg_one_zsmul]

end SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
