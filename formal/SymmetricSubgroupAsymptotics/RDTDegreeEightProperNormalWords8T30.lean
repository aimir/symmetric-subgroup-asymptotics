import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry8T30

/-! One selected source: actual proper ambient normal generation from checked words. -/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T30
open BinaryNormal8T30
local instance : Group Source := BinaryMenuCayley8T30.group

theorem normal_bound_0 : MarkedC4.normalGen N0.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N0.kernel
    N0.normalGenerators N0.state.generated).trans (by decide)

theorem normal_bound_1 : MarkedC4.normalGen N1.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N1.kernel
    N1.normalGenerators N1.state.generated).trans (by decide)

theorem normal_bound_2 : MarkedC4.normalGen N2.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N2.kernel
    N2.normalGenerators N2.state.generated).trans (by decide)

private def selected3 : Fin 1 → Fin 3 := ![2]
private def words3 : Fin 3 → List (Source × Fin 1) := ![
  [(⟨0⟩,0),(⟨2⟩,0)],
  [(⟨0⟩,0),(⟨1⟩,0)],
  [(⟨2⟩,0)]]
private theorem words3_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N3.normalGenerators ∘ selected3) (words3 j) =
      N3.normalGenerators j := by decide +kernel
theorem normal_bound_3 : MarkedC4.normalGen N3.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N3.kernel
    N3.normalGenerators N3.state.generated selected3 words3 words3_checked).trans (by decide)

theorem normal_bound_4 : MarkedC4.normalGen N4.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N4.kernel
    N4.normalGenerators N4.state.generated).trans (by decide)

private def selected5 : Fin 1 → Fin 3 := ![2]
private def words5 : Fin 3 → List (Source × Fin 1) := ![
  [(⟨0⟩,0),(⟨9⟩,0)],
  [(⟨0⟩,0),(⟨2⟩,0)],
  [(⟨10⟩,0)]]
private theorem words5_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N5.normalGenerators ∘ selected5) (words5 j) =
      N5.normalGenerators j := by decide +kernel
theorem normal_bound_5 : MarkedC4.normalGen N5.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N5.kernel
    N5.normalGenerators N5.state.generated selected5 words5 words5_checked).trans (by decide)

theorem normal_bound_6 : MarkedC4.normalGen N6.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N6.kernel
    N6.normalGenerators N6.state.generated).trans (by decide)

private def selected7 : Fin 1 → Fin 3 := ![0]
private def words7 : Fin 3 → List (Source × Fin 1) := ![
  [(⟨18⟩,0)],
  [(⟨0⟩,0),(⟨2⟩,0)],
  [(⟨2⟩,0)]]
private theorem words7_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N7.normalGenerators ∘ selected7) (words7 j) =
      N7.normalGenerators j := by decide +kernel
theorem normal_bound_7 : MarkedC4.normalGen N7.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N7.kernel
    N7.normalGenerators N7.state.generated selected7 words7 words7_checked).trans (by decide)

private def selected8 : Fin 2 → Fin 4 := ![0,1]
private def words8 : Fin 4 → List (Source × Fin 2) := ![
  [(⟨9⟩,0)],
  [(⟨18⟩,1)],
  [(⟨0⟩,0),(⟨9⟩,0)],
  [(⟨2⟩,1)]]
private theorem words8_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N8.normalGenerators ∘ selected8) (words8 j) =
      N8.normalGenerators j := by decide +kernel
theorem normal_bound_8 : MarkedC4.normalGen N8.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N8.kernel
    N8.normalGenerators N8.state.generated selected8 words8 words8_checked).trans (by decide)

private def selected9 : Fin 1 → Fin 4 := ![1]
private def words9 : Fin 4 → List (Source × Fin 1) := ![
  [(⟨0⟩,0),(⟨0⟩,0),(⟨0⟩,0),(⟨3⟩,0)],
  [(⟨0⟩,0)],
  [(⟨0⟩,0),(⟨9⟩,0)],
  [(⟨0⟩,0),(⟨0⟩,0),(⟨0⟩,0),(⟨8⟩,0)]]
private theorem words9_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N9.normalGenerators ∘ selected9) (words9 j) =
      N9.normalGenerators j := by decide +kernel
theorem normal_bound_9 : MarkedC4.normalGen N9.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N9.kernel
    N9.normalGenerators N9.state.generated selected9 words9 words9_checked).trans (by decide)

theorem normal_bound_10 : MarkedC4.normalGen N10.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N10.kernel
    N10.normalGenerators N10.state.generated).trans (by decide)

private def selected11 : Fin 2 → Fin 5 := ![0,2]
private def words11 : Fin 5 → List (Source × Fin 2) := ![
  [(⟨18⟩,0)],
  [(⟨10⟩,0)],
  [(⟨25⟩,1)],
  [(⟨2⟩,0)],
  [(⟨0⟩,1)]]
private theorem words11_checked : ∀ j,
    RDTDegreeEightNormalWords.eval (N11.normalGenerators ∘ selected11) (words11 j) =
      N11.normalGenerators j := by decide +kernel
theorem normal_bound_11 : MarkedC4.normalGen N11.kernel ≤ 2 :=
  (RDTDegreeEightNormalWords.normalGen_le_of_words N11.kernel
    N11.normalGenerators N11.state.generated selected11 words11 words11_checked).trans (by decide)

theorem normal_bound_12 (hproper : N12.kernel ≠ ⊤) : MarkedC4.normalGen N12.kernel ≤ 2 := by
  exact False.elim (hproper (Subgroup.eq_top_of_card_eq _ (N12.kernel_card.trans source_card.symm)))

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
  · exact normal_bound_12 hproper

end SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T30

end
