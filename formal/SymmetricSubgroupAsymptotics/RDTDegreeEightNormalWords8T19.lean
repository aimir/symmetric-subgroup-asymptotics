import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T19

/-! One selected source: actual ambient normal generation from checked words. -/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T19
open BinaryNormal8T19
local instance : Group Source := BinaryMenuCayley8T19.group

theorem normal_bound_0 : MarkedC4.normalGen N0.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N0.kernel
    N0.normalGenerators N0.state.generated).trans (by decide)

theorem normal_bound_1 : MarkedC4.normalGen N1.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N1.kernel
    N1.normalGenerators N1.state.generated).trans (by decide)

theorem normal_bound_2 : MarkedC4.normalGen N2.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N2.kernel
    N2.normalGenerators N2.state.generated).trans (by decide)

theorem normal_bound_3 : MarkedC4.normalGen N3.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N3.kernel
    N3.normalGenerators N3.state.generated).trans (by decide)

theorem normal_bound_4 : MarkedC4.normalGen N4.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N4.kernel
    N4.normalGenerators N4.state.generated).trans (by decide)

theorem normal_bound_5 : MarkedC4.normalGen N5.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N5.kernel
    N5.normalGenerators N5.state.generated).trans (by decide)

theorem normal_bound_6 : MarkedC4.normalGen N6.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N6.kernel
    N6.normalGenerators N6.state.generated).trans (by decide)

theorem normal_bound_7 : MarkedC4.normalGen N7.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N7.kernel
    N7.normalGenerators N7.state.generated).trans (by decide)

theorem normal_bound_8 : MarkedC4.normalGen N8.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N8.kernel
    N8.normalGenerators N8.state.generated).trans (by decide)

theorem normal_bound_9 : MarkedC4.normalGen N9.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N9.kernel
    N9.normalGenerators N9.state.generated).trans (by decide)

private def selected10 : Fin 2 → Fin 4 := ![0,2]
private def words10 : Fin 4 → List (Source × Fin 2) := ![
  [(⟨0⟩,0)],
  [(⟨0⟩,1),(⟨1⟩,1)],
  [(⟨2⟩,1)],
  [(⟨0⟩,1),(⟨3⟩,1)]]
private theorem words10_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N10.normalGenerators ∘ selected10) (words10 j) =
      N10.normalGenerators j := by decide +kernel
theorem normal_bound_10 : MarkedC4.normalGen N10.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N10.kernel
    N10.normalGenerators N10.state.generated selected10 words10 words10_checked).trans (by decide)

private def selected11 : Fin 2 → Fin 4 := ![0,2]
private def words11 : Fin 4 → List (Source × Fin 2) := ![
  [(⟨4⟩,0)],
  [(⟨0⟩,1),(⟨2⟩,1)],
  [(⟨2⟩,1)],
  [(⟨0⟩,1),(⟨3⟩,1)]]
private theorem words11_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N11.normalGenerators ∘ selected11) (words11 j) =
      N11.normalGenerators j := by decide +kernel
theorem normal_bound_11 : MarkedC4.normalGen N11.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N11.kernel
    N11.normalGenerators N11.state.generated selected11 words11 words11_checked).trans (by decide)

theorem all_normal_bound (N : Subgroup Source) [N.Normal] :
    MarkedC4.normalGen N ≤ 3 := by
  obtain ⟨i,rfl⟩ := complete N
  fin_cases i
  · exact normal_bound_0
  · exact normal_bound_1
  · exact normal_bound_2
  · exact normal_bound_3
  · exact normal_bound_4
  · exact normal_bound_5
  · exact normal_bound_6
  · exact normal_bound_7
  · exact normal_bound_8
  · exact normal_bound_9
  · exact normal_bound_10
  · exact normal_bound_11

end SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T19

end
