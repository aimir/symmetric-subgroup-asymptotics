import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialData

set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial

theorem labels_case_0 : ∀ a b : Fin 32,
 colour 0 a = colour 0 b → rank 0 a = rank 0 b → a = b := by decide
theorem advance_case_0 : ∀ a b : Fin 32,
 colour 0 a = colour 0 b → rank 0 a < rank 0 b →
 colour 0 (next 0 a) = colour 0 a ∧ rank 0 (next 0 a) = rank 0 a + 1 := by decide
theorem paths_case_0 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 0) (successorPath 0 a) a = some (next 0 a) := by decide

theorem labels_case_1 : ∀ a b : Fin 32,
 colour 1 a = colour 1 b → rank 1 a = rank 1 b → a = b := by decide
theorem advance_case_1 : ∀ a b : Fin 32,
 colour 1 a = colour 1 b → rank 1 a < rank 1 b →
 colour 1 (next 1 a) = colour 1 a ∧ rank 1 (next 1 a) = rank 1 a + 1 := by decide
theorem paths_case_1 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 1) (successorPath 1 a) a = some (next 1 a) := by decide

theorem labels_case_2 : ∀ a b : Fin 32,
 colour 2 a = colour 2 b → rank 2 a = rank 2 b → a = b := by decide
theorem advance_case_2 : ∀ a b : Fin 32,
 colour 2 a = colour 2 b → rank 2 a < rank 2 b →
 colour 2 (next 2 a) = colour 2 a ∧ rank 2 (next 2 a) = rank 2 a + 1 := by decide
theorem paths_case_2 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 2) (successorPath 2 a) a = some (next 2 a) := by decide

theorem labels_case_3 : ∀ a b : Fin 32,
 colour 3 a = colour 3 b → rank 3 a = rank 3 b → a = b := by decide
theorem advance_case_3 : ∀ a b : Fin 32,
 colour 3 a = colour 3 b → rank 3 a < rank 3 b →
 colour 3 (next 3 a) = colour 3 a ∧ rank 3 (next 3 a) = rank 3 a + 1 := by decide
theorem paths_case_3 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 3) (successorPath 3 a) a = some (next 3 a) := by decide

theorem labels_case_4 : ∀ a b : Fin 32,
 colour 4 a = colour 4 b → rank 4 a = rank 4 b → a = b := by decide
theorem advance_case_4 : ∀ a b : Fin 32,
 colour 4 a = colour 4 b → rank 4 a < rank 4 b →
 colour 4 (next 4 a) = colour 4 a ∧ rank 4 (next 4 a) = rank 4 a + 1 := by decide
theorem paths_case_4 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 4) (successorPath 4 a) a = some (next 4 a) := by decide

theorem labels_case_5 : ∀ a b : Fin 32,
 colour 5 a = colour 5 b → rank 5 a = rank 5 b → a = b := by decide
theorem advance_case_5 : ∀ a b : Fin 32,
 colour 5 a = colour 5 b → rank 5 a < rank 5 b →
 colour 5 (next 5 a) = colour 5 a ∧ rank 5 (next 5 a) = rank 5 a + 1 := by decide
theorem paths_case_5 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 5) (successorPath 5 a) a = some (next 5 a) := by decide

end SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial
