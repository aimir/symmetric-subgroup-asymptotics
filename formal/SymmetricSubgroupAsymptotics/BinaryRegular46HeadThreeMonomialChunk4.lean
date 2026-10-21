import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialData

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
namespace SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial

theorem labels_case_24 : ∀ a b : Fin 32,
 colour 24 a = colour 24 b → rank 24 a = rank 24 b → a = b := by decide
theorem advance_case_24 : ∀ a b : Fin 32,
 colour 24 a = colour 24 b → rank 24 a < rank 24 b →
 colour 24 (next 24 a) = colour 24 a ∧ rank 24 (next 24 a) = rank 24 a + 1 := by decide
theorem paths_case_24 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 24) (successorPath 24 a) a = some (next 24 a) := by decide

theorem labels_case_25 : ∀ a b : Fin 32,
 colour 25 a = colour 25 b → rank 25 a = rank 25 b → a = b := by decide
theorem advance_case_25 : ∀ a b : Fin 32,
 colour 25 a = colour 25 b → rank 25 a < rank 25 b →
 colour 25 (next 25 a) = colour 25 a ∧ rank 25 (next 25 a) = rank 25 a + 1 := by decide
theorem paths_case_25 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 25) (successorPath 25 a) a = some (next 25 a) := by decide

theorem labels_case_26 : ∀ a b : Fin 32,
 colour 26 a = colour 26 b → rank 26 a = rank 26 b → a = b := by decide
theorem advance_case_26 : ∀ a b : Fin 32,
 colour 26 a = colour 26 b → rank 26 a < rank 26 b →
 colour 26 (next 26 a) = colour 26 a ∧ rank 26 (next 26 a) = rank 26 a + 1 := by decide
theorem paths_case_26 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 26) (successorPath 26 a) a = some (next 26 a) := by decide

theorem labels_case_27 : ∀ a b : Fin 32,
 colour 27 a = colour 27 b → rank 27 a = rank 27 b → a = b := by decide
theorem advance_case_27 : ∀ a b : Fin 32,
 colour 27 a = colour 27 b → rank 27 a < rank 27 b →
 colour 27 (next 27 a) = colour 27 a ∧ rank 27 (next 27 a) = rank 27 a + 1 := by decide
theorem paths_case_27 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 27) (successorPath 27 a) a = some (next 27 a) := by decide

theorem labels_case_28 : ∀ a b : Fin 32,
 colour 28 a = colour 28 b → rank 28 a = rank 28 b → a = b := by decide
theorem advance_case_28 : ∀ a b : Fin 32,
 colour 28 a = colour 28 b → rank 28 a < rank 28 b →
 colour 28 (next 28 a) = colour 28 a ∧ rank 28 (next 28 a) = rank 28 a + 1 := by decide
theorem paths_case_28 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 28) (successorPath 28 a) a = some (next 28 a) := by decide

theorem labels_case_29 : ∀ a b : Fin 32,
 colour 29 a = colour 29 b → rank 29 a = rank 29 b → a = b := by decide
theorem advance_case_29 : ∀ a b : Fin 32,
 colour 29 a = colour 29 b → rank 29 a < rank 29 b →
 colour 29 (next 29 a) = colour 29 a ∧ rank 29 (next 29 a) = rank 29 a + 1 := by decide
theorem paths_case_29 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 29) (successorPath 29 a) a = some (next 29 a) := by decide

end SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial
