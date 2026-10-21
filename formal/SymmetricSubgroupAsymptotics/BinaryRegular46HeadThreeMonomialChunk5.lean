import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialData

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
namespace SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial

theorem labels_case_30 : ∀ a b : Fin 32,
 colour 30 a = colour 30 b → rank 30 a = rank 30 b → a = b := by decide
theorem advance_case_30 : ∀ a b : Fin 32,
 colour 30 a = colour 30 b → rank 30 a < rank 30 b →
 colour 30 (next 30 a) = colour 30 a ∧ rank 30 (next 30 a) = rank 30 a + 1 := by decide
theorem paths_case_30 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 30) (successorPath 30 a) a = some (next 30 a) := by decide

theorem labels_case_31 : ∀ a b : Fin 32,
 colour 31 a = colour 31 b → rank 31 a = rank 31 b → a = b := by decide
theorem advance_case_31 : ∀ a b : Fin 32,
 colour 31 a = colour 31 b → rank 31 a < rank 31 b →
 colour 31 (next 31 a) = colour 31 a ∧ rank 31 (next 31 a) = rank 31 a + 1 := by decide
theorem paths_case_31 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 31) (successorPath 31 a) a = some (next 31 a) := by decide

theorem labels_case_32 : ∀ a b : Fin 32,
 colour 32 a = colour 32 b → rank 32 a = rank 32 b → a = b := by decide
theorem advance_case_32 : ∀ a b : Fin 32,
 colour 32 a = colour 32 b → rank 32 a < rank 32 b →
 colour 32 (next 32 a) = colour 32 a ∧ rank 32 (next 32 a) = rank 32 a + 1 := by decide
theorem paths_case_32 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 32) (successorPath 32 a) a = some (next 32 a) := by decide

theorem labels_case_33 : ∀ a b : Fin 32,
 colour 33 a = colour 33 b → rank 33 a = rank 33 b → a = b := by decide
theorem advance_case_33 : ∀ a b : Fin 32,
 colour 33 a = colour 33 b → rank 33 a < rank 33 b →
 colour 33 (next 33 a) = colour 33 a ∧ rank 33 (next 33 a) = rank 33 a + 1 := by decide
theorem paths_case_33 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 33) (successorPath 33 a) a = some (next 33 a) := by decide

theorem labels_case_34 : ∀ a b : Fin 32,
 colour 34 a = colour 34 b → rank 34 a = rank 34 b → a = b := by decide
theorem advance_case_34 : ∀ a b : Fin 32,
 colour 34 a = colour 34 b → rank 34 a < rank 34 b →
 colour 34 (next 34 a) = colour 34 a ∧ rank 34 (next 34 a) = rank 34 a + 1 := by decide
theorem paths_case_34 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 34) (successorPath 34 a) a = some (next 34 a) := by decide

theorem labels_case_35 : ∀ a b : Fin 32,
 colour 35 a = colour 35 b → rank 35 a = rank 35 b → a = b := by decide
theorem advance_case_35 : ∀ a b : Fin 32,
 colour 35 a = colour 35 b → rank 35 a < rank 35 b →
 colour 35 (next 35 a) = colour 35 a ∧ rank 35 (next 35 a) = rank 35 a + 1 := by decide
theorem paths_case_35 : ∀ a : Fin 32,
 ModuleLeadingOperatorWords.run (step 35) (successorPath 35 a) a = some (next 35 a) := by decide

end SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial
