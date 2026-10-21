import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialChunk0
import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialChunk1
import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialChunk2
import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialChunk3
import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialChunk4
import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialChunk5

set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial

theorem labels_all (c : Fin 36) : ∀ a b : Fin 32, colour c a = colour c b → rank c a = rank c b → a = b := by
 fin_cases c
 · exact labels_case_0
 · exact labels_case_1
 · exact labels_case_2
 · exact labels_case_3
 · exact labels_case_4
 · exact labels_case_5
 · exact labels_case_6
 · exact labels_case_7
 · exact labels_case_8
 · exact labels_case_9
 · exact labels_case_10
 · exact labels_case_11
 · exact labels_case_12
 · exact labels_case_13
 · exact labels_case_14
 · exact labels_case_15
 · exact labels_case_16
 · exact labels_case_17
 · exact labels_case_18
 · exact labels_case_19
 · exact labels_case_20
 · exact labels_case_21
 · exact labels_case_22
 · exact labels_case_23
 · exact labels_case_24
 · exact labels_case_25
 · exact labels_case_26
 · exact labels_case_27
 · exact labels_case_28
 · exact labels_case_29
 · exact labels_case_30
 · exact labels_case_31
 · exact labels_case_32
 · exact labels_case_33
 · exact labels_case_34
 · exact labels_case_35

theorem advance_all (c : Fin 36) : ∀ a b : Fin 32, colour c a = colour c b → rank c a < rank c b → colour c (next c a) = colour c a ∧ rank c (next c a) = rank c a + 1 := by
 fin_cases c
 · exact advance_case_0
 · exact advance_case_1
 · exact advance_case_2
 · exact advance_case_3
 · exact advance_case_4
 · exact advance_case_5
 · exact advance_case_6
 · exact advance_case_7
 · exact advance_case_8
 · exact advance_case_9
 · exact advance_case_10
 · exact advance_case_11
 · exact advance_case_12
 · exact advance_case_13
 · exact advance_case_14
 · exact advance_case_15
 · exact advance_case_16
 · exact advance_case_17
 · exact advance_case_18
 · exact advance_case_19
 · exact advance_case_20
 · exact advance_case_21
 · exact advance_case_22
 · exact advance_case_23
 · exact advance_case_24
 · exact advance_case_25
 · exact advance_case_26
 · exact advance_case_27
 · exact advance_case_28
 · exact advance_case_29
 · exact advance_case_30
 · exact advance_case_31
 · exact advance_case_32
 · exact advance_case_33
 · exact advance_case_34
 · exact advance_case_35

theorem paths_all (c : Fin 36) : ∀ a : Fin 32, ModuleLeadingOperatorWords.run (step c) (successorPath c a) a = some (next c a) := by
 fin_cases c
 · exact paths_case_0
 · exact paths_case_1
 · exact paths_case_2
 · exact paths_case_3
 · exact paths_case_4
 · exact paths_case_5
 · exact paths_case_6
 · exact paths_case_7
 · exact paths_case_8
 · exact paths_case_9
 · exact paths_case_10
 · exact paths_case_11
 · exact paths_case_12
 · exact paths_case_13
 · exact paths_case_14
 · exact paths_case_15
 · exact paths_case_16
 · exact paths_case_17
 · exact paths_case_18
 · exact paths_case_19
 · exact paths_case_20
 · exact paths_case_21
 · exact paths_case_22
 · exact paths_case_23
 · exact paths_case_24
 · exact paths_case_25
 · exact paths_case_26
 · exact paths_case_27
 · exact paths_case_28
 · exact paths_case_29
 · exact paths_case_30
 · exact paths_case_31
 · exact paths_case_32
 · exact paths_case_33
 · exact paths_case_34
 · exact paths_case_35

private theorem coverage_case_0 : ∀ b c : Fin 16, 0 < b → b < c →
 ¬TopRel 0 b → ¬TopRel b 0 → ¬TopRel 0 c → ¬TopRel c 0 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 0 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_1 : ∀ b c : Fin 16, 1 < b → b < c →
 ¬TopRel 1 b → ¬TopRel b 1 → ¬TopRel 1 c → ¬TopRel c 1 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 1 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_2 : ∀ b c : Fin 16, 2 < b → b < c →
 ¬TopRel 2 b → ¬TopRel b 2 → ¬TopRel 2 c → ¬TopRel c 2 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 2 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_3 : ∀ b c : Fin 16, 3 < b → b < c →
 ¬TopRel 3 b → ¬TopRel b 3 → ¬TopRel 3 c → ¬TopRel c 3 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 3 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_4 : ∀ b c : Fin 16, 4 < b → b < c →
 ¬TopRel 4 b → ¬TopRel b 4 → ¬TopRel 4 c → ¬TopRel c 4 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 4 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_5 : ∀ b c : Fin 16, 5 < b → b < c →
 ¬TopRel 5 b → ¬TopRel b 5 → ¬TopRel 5 c → ¬TopRel c 5 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 5 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_6 : ∀ b c : Fin 16, 6 < b → b < c →
 ¬TopRel 6 b → ¬TopRel b 6 → ¬TopRel 6 c → ¬TopRel c 6 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 6 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_7 : ∀ b c : Fin 16, 7 < b → b < c →
 ¬TopRel 7 b → ¬TopRel b 7 → ¬TopRel 7 c → ¬TopRel c 7 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 7 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_8 : ∀ b c : Fin 16, 8 < b → b < c →
 ¬TopRel 8 b → ¬TopRel b 8 → ¬TopRel 8 c → ¬TopRel c 8 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 8 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_9 : ∀ b c : Fin 16, 9 < b → b < c →
 ¬TopRel 9 b → ¬TopRel b 9 → ¬TopRel 9 c → ¬TopRel c 9 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 9 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_10 : ∀ b c : Fin 16, 10 < b → b < c →
 ¬TopRel 10 b → ¬TopRel b 10 → ¬TopRel 10 c → ¬TopRel c 10 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 10 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_11 : ∀ b c : Fin 16, 11 < b → b < c →
 ¬TopRel 11 b → ¬TopRel b 11 → ¬TopRel 11 c → ¬TopRel c 11 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 11 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_12 : ∀ b c : Fin 16, 12 < b → b < c →
 ¬TopRel 12 b → ¬TopRel b 12 → ¬TopRel 12 c → ¬TopRel c 12 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 12 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_13 : ∀ b c : Fin 16, 13 < b → b < c →
 ¬TopRel 13 b → ¬TopRel b 13 → ¬TopRel 13 c → ¬TopRel c 13 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 13 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_14 : ∀ b c : Fin 16, 14 < b → b < c →
 ¬TopRel 14 b → ¬TopRel b 14 → ¬TopRel 14 c → ¬TopRel c 14 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 14 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

private theorem coverage_case_15 : ∀ b c : Fin 16, 15 < b → b < c →
 ¬TopRel 15 b → ¬TopRel b 15 → ¬TopRel 15 c → ¬TopRel c 15 → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = 15 ∧ labels j 1 = b ∧ labels j 2 = c := by decide

theorem sorted_triple_coverage : ∀ a b c : Fin 16, a < b → b < c →
 ¬TopRel a b → ¬TopRel b a → ¬TopRel a c → ¬TopRel c a → ¬TopRel b c → ¬TopRel c b →
 ∃ j : Fin 36, labels j 0 = a ∧ labels j 1 = b ∧ labels j 2 = c := by
 intro a
 fin_cases a
 · exact coverage_case_0
 · exact coverage_case_1
 · exact coverage_case_2
 · exact coverage_case_3
 · exact coverage_case_4
 · exact coverage_case_5
 · exact coverage_case_6
 · exact coverage_case_7
 · exact coverage_case_8
 · exact coverage_case_9
 · exact coverage_case_10
 · exact coverage_case_11
 · exact coverage_case_12
 · exact coverage_case_13
 · exact coverage_case_14
 · exact coverage_case_15

end SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial
