import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialData

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
namespace SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial

theorem labels_case_18 : ∀ a b : Fin 32,
 colour 18 a = colour 18 b → rank 18 a = rank 18 b → a = b := by decide
theorem advance_case_18 : ∀ a b : Fin 32,
 colour 18 a = colour 18 b → rank 18 a < rank 18 b →
 colour 18 (next 18 a) = colour 18 a ∧ rank 18 (next 18 a) = rank 18 a + 1 := by decide
theorem paths_case_18 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 18) (successorPath 18 a) a = some (next 18 a) := by decide

theorem labels_case_19 : ∀ a b : Fin 32,
 colour 19 a = colour 19 b → rank 19 a = rank 19 b → a = b := by decide
theorem advance_case_19 : ∀ a b : Fin 32,
 colour 19 a = colour 19 b → rank 19 a < rank 19 b →
 colour 19 (next 19 a) = colour 19 a ∧ rank 19 (next 19 a) = rank 19 a + 1 := by decide
theorem paths_case_19 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 19) (successorPath 19 a) a = some (next 19 a) := by decide

theorem labels_case_20 : ∀ a b : Fin 32,
 colour 20 a = colour 20 b → rank 20 a = rank 20 b → a = b := by decide
theorem advance_case_20 : ∀ a b : Fin 32,
 colour 20 a = colour 20 b → rank 20 a < rank 20 b →
 colour 20 (next 20 a) = colour 20 a ∧ rank 20 (next 20 a) = rank 20 a + 1 := by decide
theorem paths_case_20 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 20) (successorPath 20 a) a = some (next 20 a) := by decide

theorem labels_case_21 : ∀ a b : Fin 32,
 colour 21 a = colour 21 b → rank 21 a = rank 21 b → a = b := by decide
theorem advance_case_21 : ∀ a b : Fin 32,
 colour 21 a = colour 21 b → rank 21 a < rank 21 b →
 colour 21 (next 21 a) = colour 21 a ∧ rank 21 (next 21 a) = rank 21 a + 1 := by decide
theorem paths_case_21 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 21) (successorPath 21 a) a = some (next 21 a) := by decide

theorem labels_case_22 : ∀ a b : Fin 32,
 colour 22 a = colour 22 b → rank 22 a = rank 22 b → a = b := by decide
theorem advance_case_22 : ∀ a b : Fin 32,
 colour 22 a = colour 22 b → rank 22 a < rank 22 b →
 colour 22 (next 22 a) = colour 22 a ∧ rank 22 (next 22 a) = rank 22 a + 1 := by decide
theorem paths_case_22 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 22) (successorPath 22 a) a = some (next 22 a) := by decide

theorem labels_case_23 : ∀ a b : Fin 32,
 colour 23 a = colour 23 b → rank 23 a = rank 23 b → a = b := by decide
theorem advance_case_23 : ∀ a b : Fin 32,
 colour 23 a = colour 23 b → rank 23 a < rank 23 b →
 colour 23 (next 23 a) = colour 23 a ∧ rank 23 (next 23 a) = rank 23 a + 1 := by decide
theorem paths_case_23 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 23) (successorPath 23 a) a = some (next 23 a) := by decide

end SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial
