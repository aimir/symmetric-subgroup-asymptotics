import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSelectedTraceFirstStep
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! Only the remaining ten recorded transitions of the primary-selected
M22 word a³b² at point zero. Each private letter application follows
the literal pinned cycle, or fixes a point outside that cycle. The first
transition is imported from the checked pilot. No new trajectory, other
word, whole-action table or permutation-power decision is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSelectedTraceTransitions
open CFSG.Models.Mathieu22Construction CFSGMathieuTwentyTwoSelectedTraceFirstStep

private theorem letter_1_0 : b (14 : Fin 22) = 2 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (14 : Fin 22) = 14 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (14 : Fin 22) = 14 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (14 : Fin 22) = 2 := by
    exact List.formPerm_apply_getElem ([2,14] : List (Fin 22)) (by decide) 1 (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (2 : Fin 22) = 2 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_1_1 : b (2 : Fin 22) = 14 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (2 : Fin 22) = 2 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (2 : Fin 22) = 2 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (2 : Fin 22) = 14 := by
    exact List.formPerm_apply_lt_getElem ([2,14] : List (Fin 22)) (by decide) 0 (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (14 : Fin 22) = 14 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_1_2 : a (14 : Fin 22) = 21 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (14 : Fin 22) = 14 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (14 : Fin 22) = 14 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (14 : Fin 22) = 21 := by
    exact List.formPerm_apply_lt_getElem ([1,14,21,10,18] : List (Fin 22)) (by decide) 1 (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (21 : Fin 22) = 21 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_1_3 : a (21 : Fin 22) = 10 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (21 : Fin 22) = 21 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (21 : Fin 22) = 21 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (21 : Fin 22) = 10 := by
    exact List.formPerm_apply_lt_getElem ([1,14,21,10,18] : List (Fin 22)) (by decide) 2 (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (10 : Fin 22) = 10 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_1_4 : a (10 : Fin 22) = 18 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (10 : Fin 22) = 10 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (10 : Fin 22) = 10 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (10 : Fin 22) = 18 := by
    exact List.formPerm_apply_lt_getElem ([1,14,21,10,18] : List (Fin 22)) (by decide) 3 (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (18 : Fin 22) = 18 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem word_step_1 : selectedWord (14 : Fin 22) = 18 := by
  simp only [selectedWord, pow_succ, pow_zero, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, letter_1_0, letter_1_1, letter_1_2, letter_1_3, letter_1_4]

private theorem letter_2_0 : b (18 : Fin 22) = 8 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (18 : Fin 22) = 18 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (18 : Fin 22) = 18 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (18 : Fin 22) = 18 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (18 : Fin 22) = 8 := by
    exact List.formPerm_apply_lt_getElem ([0,17,10,19,18,8,3,1] : List (Fin 22)) (by decide) 4 (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_2_1 : b (8 : Fin 22) = 3 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (8 : Fin 22) = 8 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (8 : Fin 22) = 8 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (8 : Fin 22) = 8 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (8 : Fin 22) = 3 := by
    exact List.formPerm_apply_lt_getElem ([0,17,10,19,18,8,3,1] : List (Fin 22)) (by decide) 5 (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_2_2 : a (3 : Fin 22) = 13 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (3 : Fin 22) = 13 := by
    exact List.formPerm_apply_lt_getElem ([3,13,9,19,20] : List (Fin 22)) (by decide) 0 (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (13 : Fin 22) = 13 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (13 : Fin 22) = 13 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (13 : Fin 22) = 13 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_2_3 : a (13 : Fin 22) = 9 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (13 : Fin 22) = 9 := by
    exact List.formPerm_apply_lt_getElem ([3,13,9,19,20] : List (Fin 22)) (by decide) 1 (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (9 : Fin 22) = 9 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (9 : Fin 22) = 9 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (9 : Fin 22) = 9 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_2_4 : a (9 : Fin 22) = 19 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (9 : Fin 22) = 19 := by
    exact List.formPerm_apply_lt_getElem ([3,13,9,19,20] : List (Fin 22)) (by decide) 2 (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (19 : Fin 22) = 19 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (19 : Fin 22) = 19 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (19 : Fin 22) = 19 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem word_step_2 : selectedWord (18 : Fin 22) = 19 := by
  simp only [selectedWord, pow_succ, pow_zero, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, letter_2_0, letter_2_1, letter_2_2, letter_2_3, letter_2_4]

private theorem letter_3_0 : b (19 : Fin 22) = 18 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (19 : Fin 22) = 19 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (19 : Fin 22) = 19 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (19 : Fin 22) = 19 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (19 : Fin 22) = 18 := by
    exact List.formPerm_apply_lt_getElem ([0,17,10,19,18,8,3,1] : List (Fin 22)) (by decide) 3 (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_3_1 : b (18 : Fin 22) = 8 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (18 : Fin 22) = 18 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (18 : Fin 22) = 18 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (18 : Fin 22) = 18 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (18 : Fin 22) = 8 := by
    exact List.formPerm_apply_lt_getElem ([0,17,10,19,18,8,3,1] : List (Fin 22)) (by decide) 4 (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_3_2 : a (8 : Fin 22) = 16 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (8 : Fin 22) = 8 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (8 : Fin 22) = 16 := by
    exact List.formPerm_apply_lt_getElem ([2,7,8,16,12] : List (Fin 22)) (by decide) 2 (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (16 : Fin 22) = 16 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (16 : Fin 22) = 16 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_3_3 : a (16 : Fin 22) = 12 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (16 : Fin 22) = 16 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (16 : Fin 22) = 12 := by
    exact List.formPerm_apply_lt_getElem ([2,7,8,16,12] : List (Fin 22)) (by decide) 3 (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (12 : Fin 22) = 12 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (12 : Fin 22) = 12 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_3_4 : a (12 : Fin 22) = 2 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (12 : Fin 22) = 12 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (12 : Fin 22) = 2 := by
    exact List.formPerm_apply_getElem ([2,7,8,16,12] : List (Fin 22)) (by decide) 4 (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (2 : Fin 22) = 2 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (2 : Fin 22) = 2 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem word_step_3 : selectedWord (19 : Fin 22) = 2 := by
  simp only [selectedWord, pow_succ, pow_zero, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, letter_3_0, letter_3_1, letter_3_2, letter_3_3, letter_3_4]

private theorem letter_4_0 : b (2 : Fin 22) = 14 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (2 : Fin 22) = 2 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (2 : Fin 22) = 2 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (2 : Fin 22) = 14 := by
    exact List.formPerm_apply_lt_getElem ([2,14] : List (Fin 22)) (by decide) 0 (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (14 : Fin 22) = 14 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_4_1 : b (14 : Fin 22) = 2 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (14 : Fin 22) = 14 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (14 : Fin 22) = 14 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (14 : Fin 22) = 2 := by
    exact List.formPerm_apply_getElem ([2,14] : List (Fin 22)) (by decide) 1 (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (2 : Fin 22) = 2 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_4_2 : a (2 : Fin 22) = 7 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (2 : Fin 22) = 2 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (2 : Fin 22) = 7 := by
    exact List.formPerm_apply_lt_getElem ([2,7,8,16,12] : List (Fin 22)) (by decide) 0 (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (7 : Fin 22) = 7 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (7 : Fin 22) = 7 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_4_3 : a (7 : Fin 22) = 8 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (7 : Fin 22) = 7 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (7 : Fin 22) = 8 := by
    exact List.formPerm_apply_lt_getElem ([2,7,8,16,12] : List (Fin 22)) (by decide) 1 (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (8 : Fin 22) = 8 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (8 : Fin 22) = 8 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_4_4 : a (8 : Fin 22) = 16 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (8 : Fin 22) = 8 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (8 : Fin 22) = 16 := by
    exact List.formPerm_apply_lt_getElem ([2,7,8,16,12] : List (Fin 22)) (by decide) 2 (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (16 : Fin 22) = 16 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (16 : Fin 22) = 16 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem word_step_4 : selectedWord (2 : Fin 22) = 16 := by
  simp only [selectedWord, pow_succ, pow_zero, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, letter_4_0, letter_4_1, letter_4_2, letter_4_3, letter_4_4]

private theorem letter_5_0 : b (16 : Fin 22) = 20 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (16 : Fin 22) = 20 := by
    exact List.formPerm_apply_lt_getElem ([5,21,12,13,9,11,16,20] : List (Fin 22)) (by decide) 6 (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (20 : Fin 22) = 20 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (20 : Fin 22) = 20 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (20 : Fin 22) = 20 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_5_1 : b (20 : Fin 22) = 5 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (20 : Fin 22) = 5 := by
    exact List.formPerm_apply_getElem ([5,21,12,13,9,11,16,20] : List (Fin 22)) (by decide) 7 (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (5 : Fin 22) = 5 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (5 : Fin 22) = 5 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (5 : Fin 22) = 5 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_5_2 : a (5 : Fin 22) = 15 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (5 : Fin 22) = 5 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (5 : Fin 22) = 5 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (5 : Fin 22) = 5 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (5 : Fin 22) = 15 := by
    exact List.formPerm_apply_lt_getElem ([0,11,4,5,15] : List (Fin 22)) (by decide) 3 (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_5_3 : a (15 : Fin 22) = 0 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (15 : Fin 22) = 0 := by
    exact List.formPerm_apply_getElem ([0,11,4,5,15] : List (Fin 22)) (by decide) 4 (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_5_4 : a (0 : Fin 22) = 11 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (0 : Fin 22) = 0 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (0 : Fin 22) = 0 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (0 : Fin 22) = 0 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (0 : Fin 22) = 11 := by
    exact List.formPerm_apply_lt_getElem ([0,11,4,5,15] : List (Fin 22)) (by decide) 0 (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem word_step_5 : selectedWord (16 : Fin 22) = 11 := by
  simp only [selectedWord, pow_succ, pow_zero, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, letter_5_0, letter_5_1, letter_5_2, letter_5_3, letter_5_4]

private theorem letter_6_0 : b (11 : Fin 22) = 16 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (11 : Fin 22) = 16 := by
    exact List.formPerm_apply_lt_getElem ([5,21,12,13,9,11,16,20] : List (Fin 22)) (by decide) 5 (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (16 : Fin 22) = 16 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (16 : Fin 22) = 16 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (16 : Fin 22) = 16 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_6_1 : b (16 : Fin 22) = 20 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (16 : Fin 22) = 20 := by
    exact List.formPerm_apply_lt_getElem ([5,21,12,13,9,11,16,20] : List (Fin 22)) (by decide) 6 (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (20 : Fin 22) = 20 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (20 : Fin 22) = 20 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (20 : Fin 22) = 20 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_6_2 : a (20 : Fin 22) = 3 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (20 : Fin 22) = 3 := by
    exact List.formPerm_apply_getElem ([3,13,9,19,20] : List (Fin 22)) (by decide) 4 (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (3 : Fin 22) = 3 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (3 : Fin 22) = 3 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (3 : Fin 22) = 3 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_6_3 : a (3 : Fin 22) = 13 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (3 : Fin 22) = 13 := by
    exact List.formPerm_apply_lt_getElem ([3,13,9,19,20] : List (Fin 22)) (by decide) 0 (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (13 : Fin 22) = 13 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (13 : Fin 22) = 13 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (13 : Fin 22) = 13 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_6_4 : a (13 : Fin 22) = 9 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (13 : Fin 22) = 9 := by
    exact List.formPerm_apply_lt_getElem ([3,13,9,19,20] : List (Fin 22)) (by decide) 1 (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (9 : Fin 22) = 9 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (9 : Fin 22) = 9 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (9 : Fin 22) = 9 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem word_step_6 : selectedWord (11 : Fin 22) = 9 := by
  simp only [selectedWord, pow_succ, pow_zero, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, letter_6_0, letter_6_1, letter_6_2, letter_6_3, letter_6_4]

private theorem letter_7_0 : b (9 : Fin 22) = 11 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (9 : Fin 22) = 11 := by
    exact List.formPerm_apply_lt_getElem ([5,21,12,13,9,11,16,20] : List (Fin 22)) (by decide) 4 (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (11 : Fin 22) = 11 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (11 : Fin 22) = 11 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (11 : Fin 22) = 11 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_7_1 : b (11 : Fin 22) = 16 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (11 : Fin 22) = 16 := by
    exact List.formPerm_apply_lt_getElem ([5,21,12,13,9,11,16,20] : List (Fin 22)) (by decide) 5 (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (16 : Fin 22) = 16 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (16 : Fin 22) = 16 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (16 : Fin 22) = 16 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_7_2 : a (16 : Fin 22) = 12 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (16 : Fin 22) = 16 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (16 : Fin 22) = 12 := by
    exact List.formPerm_apply_lt_getElem ([2,7,8,16,12] : List (Fin 22)) (by decide) 3 (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (12 : Fin 22) = 12 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (12 : Fin 22) = 12 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_7_3 : a (12 : Fin 22) = 2 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (12 : Fin 22) = 12 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (12 : Fin 22) = 2 := by
    exact List.formPerm_apply_getElem ([2,7,8,16,12] : List (Fin 22)) (by decide) 4 (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (2 : Fin 22) = 2 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (2 : Fin 22) = 2 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_7_4 : a (2 : Fin 22) = 7 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (2 : Fin 22) = 2 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (2 : Fin 22) = 7 := by
    exact List.formPerm_apply_lt_getElem ([2,7,8,16,12] : List (Fin 22)) (by decide) 0 (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (7 : Fin 22) = 7 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (7 : Fin 22) = 7 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem word_step_7 : selectedWord (9 : Fin 22) = 7 := by
  simp only [selectedWord, pow_succ, pow_zero, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, letter_7_0, letter_7_1, letter_7_2, letter_7_3, letter_7_4]

private theorem letter_8_0 : b (7 : Fin 22) = 6 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (7 : Fin 22) = 7 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (7 : Fin 22) = 6 := by
    exact List.formPerm_apply_lt_getElem ([4,7,6,15] : List (Fin 22)) (by decide) 1 (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_8_1 : b (6 : Fin 22) = 15 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (6 : Fin 22) = 15 := by
    exact List.formPerm_apply_lt_getElem ([4,7,6,15] : List (Fin 22)) (by decide) 2 (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_8_2 : a (15 : Fin 22) = 0 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (15 : Fin 22) = 0 := by
    exact List.formPerm_apply_getElem ([0,11,4,5,15] : List (Fin 22)) (by decide) 4 (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_8_3 : a (0 : Fin 22) = 11 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (0 : Fin 22) = 0 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (0 : Fin 22) = 0 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (0 : Fin 22) = 0 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (0 : Fin 22) = 11 := by
    exact List.formPerm_apply_lt_getElem ([0,11,4,5,15] : List (Fin 22)) (by decide) 0 (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_8_4 : a (11 : Fin 22) = 4 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (11 : Fin 22) = 11 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (11 : Fin 22) = 11 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (11 : Fin 22) = 11 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (11 : Fin 22) = 4 := by
    exact List.formPerm_apply_lt_getElem ([0,11,4,5,15] : List (Fin 22)) (by decide) 1 (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem word_step_8 : selectedWord (7 : Fin 22) = 4 := by
  simp only [selectedWord, pow_succ, pow_zero, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, letter_8_0, letter_8_1, letter_8_2, letter_8_3, letter_8_4]

private theorem letter_9_0 : b (4 : Fin 22) = 7 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (4 : Fin 22) = 4 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (4 : Fin 22) = 7 := by
    exact List.formPerm_apply_lt_getElem ([4,7,6,15] : List (Fin 22)) (by decide) 0 (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (7 : Fin 22) = 7 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (7 : Fin 22) = 7 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_9_1 : b (7 : Fin 22) = 6 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (7 : Fin 22) = 7 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (7 : Fin 22) = 6 := by
    exact List.formPerm_apply_lt_getElem ([4,7,6,15] : List (Fin 22)) (by decide) 1 (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_9_2 : a (6 : Fin 22) = 6 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_9_3 : a (6 : Fin 22) = 6 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_9_4 : a (6 : Fin 22) = 6 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem word_step_9 : selectedWord (4 : Fin 22) = 6 := by
  simp only [selectedWord, pow_succ, pow_zero, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, letter_9_0, letter_9_1, letter_9_2]

private theorem letter_10_0 : b (6 : Fin 22) = 15 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (6 : Fin 22) = 6 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (6 : Fin 22) = 15 := by
    exact List.formPerm_apply_lt_getElem ([4,7,6,15] : List (Fin 22)) (by decide) 2 (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_10_1 : b (15 : Fin 22) = 4 := by
  have h3 : List.formPerm ([5,21,12,13,9,11,16,20] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([4,7,6,15] : List (Fin 22)) (15 : Fin 22) = 4 := by
    exact List.formPerm_apply_getElem ([4,7,6,15] : List (Fin 22)) (by decide) 3 (by decide)
  have h1 : List.formPerm ([2,14] : List (Fin 22)) (4 : Fin 22) = 4 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) (4 : Fin 22) = 4 := by
    exact List.formPerm_apply_of_notMem (by decide)
  simp only [b, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_10_2 : a (4 : Fin 22) = 5 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (4 : Fin 22) = 4 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (4 : Fin 22) = 4 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (4 : Fin 22) = 4 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (4 : Fin 22) = 5 := by
    exact List.formPerm_apply_lt_getElem ([0,11,4,5,15] : List (Fin 22)) (by decide) 2 (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_10_3 : a (5 : Fin 22) = 15 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (5 : Fin 22) = 5 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (5 : Fin 22) = 5 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (5 : Fin 22) = 5 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (5 : Fin 22) = 15 := by
    exact List.formPerm_apply_lt_getElem ([0,11,4,5,15] : List (Fin 22)) (by decide) 3 (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem letter_10_4 : a (15 : Fin 22) = 0 := by
  have h3 : List.formPerm ([3,13,9,19,20] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h2 : List.formPerm ([2,7,8,16,12] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) (15 : Fin 22) = 15 := by
    exact List.formPerm_apply_of_notMem (by decide)
  have h0 : List.formPerm ([0,11,4,5,15] : List (Fin 22)) (15 : Fin 22) = 0 := by
    exact List.formPerm_apply_getElem ([0,11,4,5,15] : List (Fin 22)) (by decide) 4 (by decide)
  simp only [a, Equiv.Perm.mul_apply, h3, h2, h1, h0]

private theorem word_step_10 : selectedWord (6 : Fin 22) = 0 := by
  simp only [selectedWord, pow_succ, pow_zero, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, letter_10_0, letter_10_1, letter_10_2, letter_10_3, letter_10_4]

-- Prove the power calculation with an ABSTRACT permutation. The concrete
-- literal cycle definitions never enter this induction or its simp proof.
private theorem pow_apply_eq_point {X : Type*} (g : Equiv.Perm X) (d : ℕ)
    (v : Fin (d + 1) → X)
    (hstep : ∀ i : Fin d, g (v i.castSucc) = v i.succ)
    (i : Fin (d + 1)) : (g ^ i.val) (v 0) = v i := by
  have h : ∀ j : ℕ, ∀ hj : j < d + 1,
      (g ^ j) (v 0) = v ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      have hjd : j < d := by omega
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
      exact hstep ⟨j, hjd⟩
  exact h i.val i.isLt

/-- The exact selected return at eleven, obtained only from the eleven
checked consecutive steps of the SAME actual pinned word. -/
theorem return_eleven : (selectedWord ^ 11) (0 : Fin 22) = 0 := by
  let v : Fin 12 → Fin 22 := ![0,14,18,19,2,16,11,9,7,4,6,0]
  have hstep : ∀ i : Fin 11, selectedWord (v i.castSucc) = v i.succ :=
    Fin.cases first_step
      (Fin.cases word_step_1
        (Fin.cases word_step_2
          (Fin.cases word_step_3
            (Fin.cases word_step_4
              (Fin.cases word_step_5
                (Fin.cases word_step_6
                  (Fin.cases word_step_7
                    (Fin.cases word_step_8
                      (Fin.cases word_step_9
                        (Fin.cases word_step_10 (fun i => Fin.elim0 i)))))))))))
  have h := pow_apply_eq_point selectedWord 11 v hstep ⟨11, by decide⟩
  exact h

/-- The first checked transition already gives the required nonreturn. -/
theorem moved_zero : selectedWord (0 : Fin 22) ≠ 0 := by
  rw [first_step]
  decide

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSelectedTraceTransitions
