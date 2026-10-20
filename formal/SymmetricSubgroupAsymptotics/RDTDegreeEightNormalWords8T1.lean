import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T1

/-! One selected source: actual ambient normal generation from checked words. -/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T1
open BinaryNormal8T1
local instance : Group Source := BinaryMenuCayley8T1.group

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

theorem all_normal_bound (N : Subgroup Source) [N.Normal] :
    MarkedC4.normalGen N ≤ 3 := by
  obtain ⟨i,rfl⟩ := complete N
  fin_cases i
  · exact normal_bound_0
  · exact normal_bound_1
  · exact normal_bound_2
  · exact normal_bound_3

end SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T1

end
