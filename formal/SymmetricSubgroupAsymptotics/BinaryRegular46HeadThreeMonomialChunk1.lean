import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialData

set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial

theorem labels_case_6 : ∀ a b : Fin 32,
 colour 6 a = colour 6 b → rank 6 a = rank 6 b → a = b := by decide
theorem advance_case_6 : ∀ a b : Fin 32,
 colour 6 a = colour 6 b → rank 6 a < rank 6 b →
 colour 6 (next 6 a) = colour 6 a ∧ rank 6 (next 6 a) = rank 6 a + 1 := by decide
theorem paths_case_6 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 6) (successorPath 6 a) a = some (next 6 a) := by decide

theorem labels_case_7 : ∀ a b : Fin 32,
 colour 7 a = colour 7 b → rank 7 a = rank 7 b → a = b := by decide
theorem advance_case_7 : ∀ a b : Fin 32,
 colour 7 a = colour 7 b → rank 7 a < rank 7 b →
 colour 7 (next 7 a) = colour 7 a ∧ rank 7 (next 7 a) = rank 7 a + 1 := by decide
theorem paths_case_7 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 7) (successorPath 7 a) a = some (next 7 a) := by decide

theorem labels_case_8 : ∀ a b : Fin 32,
 colour 8 a = colour 8 b → rank 8 a = rank 8 b → a = b := by decide
theorem advance_case_8 : ∀ a b : Fin 32,
 colour 8 a = colour 8 b → rank 8 a < rank 8 b →
 colour 8 (next 8 a) = colour 8 a ∧ rank 8 (next 8 a) = rank 8 a + 1 := by decide
theorem paths_case_8 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 8) (successorPath 8 a) a = some (next 8 a) := by decide

theorem labels_case_9 : ∀ a b : Fin 32,
 colour 9 a = colour 9 b → rank 9 a = rank 9 b → a = b := by decide
theorem advance_case_9 : ∀ a b : Fin 32,
 colour 9 a = colour 9 b → rank 9 a < rank 9 b →
 colour 9 (next 9 a) = colour 9 a ∧ rank 9 (next 9 a) = rank 9 a + 1 := by decide
theorem paths_case_9 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 9) (successorPath 9 a) a = some (next 9 a) := by decide

theorem labels_case_10 : ∀ a b : Fin 32,
 colour 10 a = colour 10 b → rank 10 a = rank 10 b → a = b := by decide
theorem advance_case_10 : ∀ a b : Fin 32,
 colour 10 a = colour 10 b → rank 10 a < rank 10 b →
 colour 10 (next 10 a) = colour 10 a ∧ rank 10 (next 10 a) = rank 10 a + 1 := by decide
theorem paths_case_10 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 10) (successorPath 10 a) a = some (next 10 a) := by decide

theorem labels_case_11 : ∀ a b : Fin 32,
 colour 11 a = colour 11 b → rank 11 a = rank 11 b → a = b := by decide
theorem advance_case_11 : ∀ a b : Fin 32,
 colour 11 a = colour 11 b → rank 11 a < rank 11 b →
 colour 11 (next 11 a) = colour 11 a ∧ rank 11 (next 11 a) = rank 11 a + 1 := by decide
theorem paths_case_11 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 11) (successorPath 11 a) a = some (next 11 a) := by decide

end SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial
