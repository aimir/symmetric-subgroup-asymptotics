import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialData

set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial

theorem labels_case_12 : ∀ a b : Fin 32,
 colour 12 a = colour 12 b → rank 12 a = rank 12 b → a = b := by decide
theorem advance_case_12 : ∀ a b : Fin 32,
 colour 12 a = colour 12 b → rank 12 a < rank 12 b →
 colour 12 (next 12 a) = colour 12 a ∧ rank 12 (next 12 a) = rank 12 a + 1 := by decide
theorem paths_case_12 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 12) (successorPath 12 a) a = some (next 12 a) := by decide

theorem labels_case_13 : ∀ a b : Fin 32,
 colour 13 a = colour 13 b → rank 13 a = rank 13 b → a = b := by decide
theorem advance_case_13 : ∀ a b : Fin 32,
 colour 13 a = colour 13 b → rank 13 a < rank 13 b →
 colour 13 (next 13 a) = colour 13 a ∧ rank 13 (next 13 a) = rank 13 a + 1 := by decide
theorem paths_case_13 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 13) (successorPath 13 a) a = some (next 13 a) := by decide

theorem labels_case_14 : ∀ a b : Fin 32,
 colour 14 a = colour 14 b → rank 14 a = rank 14 b → a = b := by decide
theorem advance_case_14 : ∀ a b : Fin 32,
 colour 14 a = colour 14 b → rank 14 a < rank 14 b →
 colour 14 (next 14 a) = colour 14 a ∧ rank 14 (next 14 a) = rank 14 a + 1 := by decide
theorem paths_case_14 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 14) (successorPath 14 a) a = some (next 14 a) := by decide

theorem labels_case_15 : ∀ a b : Fin 32,
 colour 15 a = colour 15 b → rank 15 a = rank 15 b → a = b := by decide
theorem advance_case_15 : ∀ a b : Fin 32,
 colour 15 a = colour 15 b → rank 15 a < rank 15 b →
 colour 15 (next 15 a) = colour 15 a ∧ rank 15 (next 15 a) = rank 15 a + 1 := by decide
theorem paths_case_15 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 15) (successorPath 15 a) a = some (next 15 a) := by decide

theorem labels_case_16 : ∀ a b : Fin 32,
 colour 16 a = colour 16 b → rank 16 a = rank 16 b → a = b := by decide
theorem advance_case_16 : ∀ a b : Fin 32,
 colour 16 a = colour 16 b → rank 16 a < rank 16 b →
 colour 16 (next 16 a) = colour 16 a ∧ rank 16 (next 16 a) = rank 16 a + 1 := by decide
theorem paths_case_16 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 16) (successorPath 16 a) a = some (next 16 a) := by decide

theorem labels_case_17 : ∀ a b : Fin 32,
 colour 17 a = colour 17 b → rank 17 a = rank 17 b → a = b := by decide
theorem advance_case_17 : ∀ a b : Fin 32,
 colour 17 a = colour 17 b → rank 17 a < rank 17 b →
 colour 17 (next 17 a) = colour 17 a ∧ rank 17 (next 17 a) = rank 17 a + 1 := by decide
theorem paths_case_17 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 17) (successorPath 17 a) a = some (next 17 a) := by decide

end SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial
