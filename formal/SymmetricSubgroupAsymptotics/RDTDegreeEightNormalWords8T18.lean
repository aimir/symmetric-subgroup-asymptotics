import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T18

/-! One selected source: actual ambient normal generation from checked words. -/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T18
open BinaryNormal8T18
local instance : Group Source := BinaryMenuCayley8T18.group

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

theorem normal_bound_10 : MarkedC4.normalGen N10.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N10.kernel
    N10.normalGenerators N10.state.generated).trans (by decide)

theorem normal_bound_11 : MarkedC4.normalGen N11.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N11.kernel
    N11.normalGenerators N11.state.generated).trans (by decide)

theorem normal_bound_12 : MarkedC4.normalGen N12.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N12.kernel
    N12.normalGenerators N12.state.generated).trans (by decide)

theorem normal_bound_13 : MarkedC4.normalGen N13.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N13.kernel
    N13.normalGenerators N13.state.generated).trans (by decide)

theorem normal_bound_14 : MarkedC4.normalGen N14.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N14.kernel
    N14.normalGenerators N14.state.generated).trans (by decide)

theorem normal_bound_15 : MarkedC4.normalGen N15.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N15.kernel
    N15.normalGenerators N15.state.generated).trans (by decide)

theorem normal_bound_16 : MarkedC4.normalGen N16.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N16.kernel
    N16.normalGenerators N16.state.generated).trans (by decide)

theorem normal_bound_17 : MarkedC4.normalGen N17.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N17.kernel
    N17.normalGenerators N17.state.generated).trans (by decide)

private def selected18 : Fin 2 → Fin 4 := ![0,1]
private def words18 : Fin 4 → List (Source × Fin 2) := ![
  [(⟨0⟩,0)],
  [(⟨0⟩,1)],
  [(⟨12⟩,0),(⟨12⟩,1)],
  [(⟨12⟩,1)]]
private theorem words18_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N18.normalGenerators ∘ selected18) (words18 j) =
      N18.normalGenerators j := by decide +kernel
theorem normal_bound_18 : MarkedC4.normalGen N18.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N18.kernel
    N18.normalGenerators N18.state.generated selected18 words18 words18_checked).trans (by decide)

private def selected19 : Fin 2 → Fin 4 := ![0,3]
private def words19 : Fin 4 → List (Source × Fin 2) := ![
  [(⟨0⟩,0)],
  [(⟨0⟩,0),(⟨0⟩,1),(⟨3⟩,1)],
  [(⟨0⟩,1),(⟨2⟩,1)],
  [(⟨2⟩,1)]]
private theorem words19_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N19.normalGenerators ∘ selected19) (words19 j) =
      N19.normalGenerators j := by decide +kernel
theorem normal_bound_19 : MarkedC4.normalGen N19.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N19.kernel
    N19.normalGenerators N19.state.generated selected19 words19 words19_checked).trans (by decide)

private def selected20 : Fin 2 → Fin 4 := ![0,3]
private def words20 : Fin 4 → List (Source × Fin 2) := ![
  [(⟨0⟩,0)],
  [(⟨0⟩,0),(⟨0⟩,1),(⟨0⟩,1)],
  [(⟨0⟩,1),(⟨1⟩,1)],
  [(⟨2⟩,1)]]
private theorem words20_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N20.normalGenerators ∘ selected20) (words20 j) =
      N20.normalGenerators j := by decide +kernel
theorem normal_bound_20 : MarkedC4.normalGen N20.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N20.kernel
    N20.normalGenerators N20.state.generated selected20 words20 words20_checked).trans (by decide)

private def selected21 : Fin 2 → Fin 4 := ![0,3]
private def words21 : Fin 4 → List (Source × Fin 2) := ![
  [(⟨0⟩,0)],
  [(⟨0⟩,0),(⟨0⟩,1),(⟨3⟩,1)],
  [(⟨12⟩,0)],
  [(⟨2⟩,1)]]
private theorem words21_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N21.normalGenerators ∘ selected21) (words21 j) =
      N21.normalGenerators j := by decide +kernel
theorem normal_bound_21 : MarkedC4.normalGen N21.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N21.kernel
    N21.normalGenerators N21.state.generated selected21 words21 words21_checked).trans (by decide)

private def selected22 : Fin 2 → Fin 4 := ![0,3]
private def words22 : Fin 4 → List (Source × Fin 2) := ![
  [(⟨0⟩,0)],
  [(⟨0⟩,0),(⟨0⟩,1),(⟨0⟩,1)],
  [(⟨12⟩,0)],
  [(⟨2⟩,1)]]
private theorem words22_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N22.normalGenerators ∘ selected22) (words22 j) =
      N22.normalGenerators j := by decide +kernel
theorem normal_bound_22 : MarkedC4.normalGen N22.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N22.kernel
    N22.normalGenerators N22.state.generated selected22 words22 words22_checked).trans (by decide)

private def selected23 : Fin 2 → Fin 4 := ![0,3]
private def words23 : Fin 4 → List (Source × Fin 2) := ![
  [(⟨0⟩,0)],
  [(⟨12⟩,0)],
  [(⟨0⟩,0),(⟨0⟩,1),(⟨2⟩,1)],
  [(⟨2⟩,1)]]
private theorem words23_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N23.normalGenerators ∘ selected23) (words23 j) =
      N23.normalGenerators j := by decide +kernel
theorem normal_bound_23 : MarkedC4.normalGen N23.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N23.kernel
    N23.normalGenerators N23.state.generated selected23 words23 words23_checked).trans (by decide)

private def selected24 : Fin 2 → Fin 4 := ![0,3]
private def words24 : Fin 4 → List (Source × Fin 2) := ![
  [(⟨0⟩,0)],
  [(⟨12⟩,0)],
  [(⟨0⟩,0),(⟨0⟩,1),(⟨0⟩,1)],
  [(⟨2⟩,1)]]
private theorem words24_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N24.normalGenerators ∘ selected24) (words24 j) =
      N24.normalGenerators j := by decide +kernel
theorem normal_bound_24 : MarkedC4.normalGen N24.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N24.kernel
    N24.normalGenerators N24.state.generated selected24 words24 words24_checked).trans (by decide)

private def selected25 : Fin 3 → Fin 5 := ![0,1,4]
private def words25 : Fin 5 → List (Source × Fin 3) := ![
  [(⟨0⟩,0)],
  [(⟨0⟩,1)],
  [(⟨12⟩,0),(⟨12⟩,1)],
  [(⟨12⟩,1)],
  [(⟨2⟩,2)]]
private theorem words25_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N25.normalGenerators ∘ selected25) (words25 j) =
      N25.normalGenerators j := by decide +kernel
theorem normal_bound_25 : MarkedC4.normalGen N25.kernel ≤ 3 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N25.kernel
    N25.normalGenerators N25.state.generated selected25 words25 words25_checked).trans (by decide)

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
  · exact normal_bound_12
  · exact normal_bound_13
  · exact normal_bound_14
  · exact normal_bound_15
  · exact normal_bound_16
  · exact normal_bound_17
  · exact normal_bound_18
  · exact normal_bound_19
  · exact normal_bound_20
  · exact normal_bound_21
  · exact normal_bound_22
  · exact normal_bound_23
  · exact normal_bound_24
  · exact normal_bound_25

end SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T18

end
