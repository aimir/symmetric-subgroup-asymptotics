import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T15

/-! One selected source: actual proper ambient normal generation from checked words. -/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T15
open BinaryNormal8T15
local instance : Group Source := BinaryMenuCayley8T15.group

theorem normal_bound_0 : MarkedC4.normalGen N0.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N0.kernel
    N0.normalGenerators N0.state.generated).trans (by decide)

theorem normal_bound_1 : MarkedC4.normalGen N1.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N1.kernel
    N1.normalGenerators N1.state.generated).trans (by decide)

theorem normal_bound_2 : MarkedC4.normalGen N2.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N2.kernel
    N2.normalGenerators N2.state.generated).trans (by decide)

theorem normal_bound_3 : MarkedC4.normalGen N3.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N3.kernel
    N3.normalGenerators N3.state.generated).trans (by decide)

theorem normal_bound_4 : MarkedC4.normalGen N4.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N4.kernel
    N4.normalGenerators N4.state.generated).trans (by decide)

theorem normal_bound_5 : MarkedC4.normalGen N5.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N5.kernel
    N5.normalGenerators N5.state.generated).trans (by decide)

theorem normal_bound_6 : MarkedC4.normalGen N6.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N6.kernel
    N6.normalGenerators N6.state.generated).trans (by decide)

theorem normal_bound_7 : MarkedC4.normalGen N7.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N7.kernel
    N7.normalGenerators N7.state.generated).trans (by decide)

theorem normal_bound_8 : MarkedC4.normalGen N8.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N8.kernel
    N8.normalGenerators N8.state.generated).trans (by decide)

theorem normal_bound_9 : MarkedC4.normalGen N9.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N9.kernel
    N9.normalGenerators N9.state.generated).trans (by decide)

theorem normal_bound_10 : MarkedC4.normalGen N10.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N10.kernel
    N10.normalGenerators N10.state.generated).trans (by decide)

theorem normal_bound_11 : MarkedC4.normalGen N11.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N11.kernel
    N11.normalGenerators N11.state.generated).trans (by decide)

private def selected12 : Fin 2 → Fin 3 := ![1,2]
private def words12 : Fin 3 → List (Source × Fin 2) := ![
  [(⟨0⟩,1),(⟨3⟩,1)],
  [(⟨4⟩,0)],
  [(⟨2⟩,1)]]
private theorem words12_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N12.normalGenerators ∘ selected12) (words12 j) =
      N12.normalGenerators j := by decide +kernel
theorem normal_bound_12 : MarkedC4.normalGen N12.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N12.kernel
    N12.normalGenerators N12.state.generated selected12 words12 words12_checked).trans (by decide)

theorem normal_bound_13 : MarkedC4.normalGen N13.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N13.kernel
    N13.normalGenerators N13.state.generated).trans (by decide)

private def selected14 : Fin 2 → Fin 3 := ![1,2]
private def words14 : Fin 3 → List (Source × Fin 2) := ![
  [(⟨0⟩,1),(⟨4⟩,1)],
  [(⟨4⟩,0)],
  [(⟨5⟩,1)]]
private theorem words14_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N14.normalGenerators ∘ selected14) (words14 j) =
      N14.normalGenerators j := by decide +kernel
theorem normal_bound_14 : MarkedC4.normalGen N14.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N14.kernel
    N14.normalGenerators N14.state.generated selected14 words14 words14_checked).trans (by decide)

theorem normal_bound_15 : MarkedC4.normalGen N15.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N15.kernel
    N15.normalGenerators N15.state.generated).trans (by decide)

theorem normal_bound_16 : MarkedC4.normalGen N16.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N16.kernel
    N16.normalGenerators N16.state.generated).trans (by decide)

theorem normal_bound_17 : MarkedC4.normalGen N17.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N17.kernel
    N17.normalGenerators N17.state.generated).trans (by decide)

theorem normal_bound_18 : MarkedC4.normalGen N18.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N18.kernel
    N18.normalGenerators N18.state.generated).trans (by decide)

theorem normal_bound_19 (hproper : N19.kernel ≠ ⊤) : MarkedC4.normalGen N19.kernel ≤ 2 := by
  exact False.elim (hproper (Subgroup.eq_top_of_card_eq _ (N19.kernel_card.trans source_card.symm)))

theorem all_normal_bound (N : Subgroup Source) [N.Normal] :
    (hproper : N ≠ ⊤) → MarkedC4.normalGen N ≤ 2 := by
  intro hproper
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
  · exact normal_bound_12
  · exact normal_bound_13
  · exact normal_bound_14
  · exact normal_bound_15
  · exact normal_bound_16
  · exact normal_bound_17
  · exact normal_bound_18
  · exact normal_bound_19 hproper

end SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T15

end
