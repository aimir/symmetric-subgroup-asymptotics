import SymmetricSubgroupAsymptotics.BinaryHeisenbergFourCentralLineData
import SymmetricSubgroupAsymptotics.SmallDerivedCentralLineNormalFBounds
import SymmetricSubgroupAsymptotics.FiniteProductSubtypeCard

/-! The centre counts use structural product fibres: each finite check
has eight kernel vectors at one fixed original top row. The final theorem
covers every original normal denominator using only three central lines. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical commutatorElement BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergFourCentralLines
open BinaryHeisenbergFourCentralModel

private def centerFibreCount : Fin 32 → ℕ := ![2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2]

private theorem center_fibre_0 : Fintype.card {a : KernelIndex // centerMask (a,0)} = centerFibreCount 0 := by
  decide +kernel

private theorem center_fibre_1 : Fintype.card {a : KernelIndex // centerMask (a,1)} = centerFibreCount 1 := by
  decide +kernel

private theorem center_fibre_2 : Fintype.card {a : KernelIndex // centerMask (a,2)} = centerFibreCount 2 := by
  decide +kernel

private theorem center_fibre_3 : Fintype.card {a : KernelIndex // centerMask (a,3)} = centerFibreCount 3 := by
  decide +kernel

private theorem center_fibre_4 : Fintype.card {a : KernelIndex // centerMask (a,4)} = centerFibreCount 4 := by
  decide +kernel

private theorem center_fibre_5 : Fintype.card {a : KernelIndex // centerMask (a,5)} = centerFibreCount 5 := by
  decide +kernel

private theorem center_fibre_6 : Fintype.card {a : KernelIndex // centerMask (a,6)} = centerFibreCount 6 := by
  decide +kernel

private theorem center_fibre_7 : Fintype.card {a : KernelIndex // centerMask (a,7)} = centerFibreCount 7 := by
  decide +kernel

private theorem center_fibre_8 : Fintype.card {a : KernelIndex // centerMask (a,8)} = centerFibreCount 8 := by
  decide +kernel

private theorem center_fibre_9 : Fintype.card {a : KernelIndex // centerMask (a,9)} = centerFibreCount 9 := by
  decide +kernel

private theorem center_fibre_10 : Fintype.card {a : KernelIndex // centerMask (a,10)} = centerFibreCount 10 := by
  decide +kernel

private theorem center_fibre_11 : Fintype.card {a : KernelIndex // centerMask (a,11)} = centerFibreCount 11 := by
  decide +kernel

private theorem center_fibre_12 : Fintype.card {a : KernelIndex // centerMask (a,12)} = centerFibreCount 12 := by
  decide +kernel

private theorem center_fibre_13 : Fintype.card {a : KernelIndex // centerMask (a,13)} = centerFibreCount 13 := by
  decide +kernel

private theorem center_fibre_14 : Fintype.card {a : KernelIndex // centerMask (a,14)} = centerFibreCount 14 := by
  decide +kernel

private theorem center_fibre_15 : Fintype.card {a : KernelIndex // centerMask (a,15)} = centerFibreCount 15 := by
  decide +kernel

private theorem center_fibre_16 : Fintype.card {a : KernelIndex // centerMask (a,16)} = centerFibreCount 16 := by
  decide +kernel

private theorem center_fibre_17 : Fintype.card {a : KernelIndex // centerMask (a,17)} = centerFibreCount 17 := by
  decide +kernel

private theorem center_fibre_18 : Fintype.card {a : KernelIndex // centerMask (a,18)} = centerFibreCount 18 := by
  decide +kernel

private theorem center_fibre_19 : Fintype.card {a : KernelIndex // centerMask (a,19)} = centerFibreCount 19 := by
  decide +kernel

private theorem center_fibre_20 : Fintype.card {a : KernelIndex // centerMask (a,20)} = centerFibreCount 20 := by
  decide +kernel

private theorem center_fibre_21 : Fintype.card {a : KernelIndex // centerMask (a,21)} = centerFibreCount 21 := by
  decide +kernel

private theorem center_fibre_22 : Fintype.card {a : KernelIndex // centerMask (a,22)} = centerFibreCount 22 := by
  decide +kernel

private theorem center_fibre_23 : Fintype.card {a : KernelIndex // centerMask (a,23)} = centerFibreCount 23 := by
  decide +kernel

private theorem center_fibre_24 : Fintype.card {a : KernelIndex // centerMask (a,24)} = centerFibreCount 24 := by
  decide +kernel

private theorem center_fibre_25 : Fintype.card {a : KernelIndex // centerMask (a,25)} = centerFibreCount 25 := by
  decide +kernel

private theorem center_fibre_26 : Fintype.card {a : KernelIndex // centerMask (a,26)} = centerFibreCount 26 := by
  decide +kernel

private theorem center_fibre_27 : Fintype.card {a : KernelIndex // centerMask (a,27)} = centerFibreCount 27 := by
  decide +kernel

private theorem center_fibre_28 : Fintype.card {a : KernelIndex // centerMask (a,28)} = centerFibreCount 28 := by
  decide +kernel

private theorem center_fibre_29 : Fintype.card {a : KernelIndex // centerMask (a,29)} = centerFibreCount 29 := by
  decide +kernel

private theorem center_fibre_30 : Fintype.card {a : KernelIndex // centerMask (a,30)} = centerFibreCount 30 := by
  decide +kernel

private theorem center_fibre_31 : Fintype.card {a : KernelIndex // centerMask (a,31)} = centerFibreCount 31 := by
  decide +kernel

private theorem center_fibre_count (i : Fin 32) :
    Fintype.card {a : KernelIndex // centerMask (a,i)} = centerFibreCount i := by
  fin_cases i
  · exact center_fibre_0
  · exact center_fibre_1
  · exact center_fibre_2
  · exact center_fibre_3
  · exact center_fibre_4
  · exact center_fibre_5
  · exact center_fibre_6
  · exact center_fibre_7
  · exact center_fibre_8
  · exact center_fibre_9
  · exact center_fibre_10
  · exact center_fibre_11
  · exact center_fibre_12
  · exact center_fibre_13
  · exact center_fibre_14
  · exact center_fibre_15
  · exact center_fibre_16
  · exact center_fibre_17
  · exact center_fibre_18
  · exact center_fibre_19
  · exact center_fibre_20
  · exact center_fibre_21
  · exact center_fibre_22
  · exact center_fibre_23
  · exact center_fibre_24
  · exact center_fibre_25
  · exact center_fibre_26
  · exact center_fibre_27
  · exact center_fibre_28
  · exact center_fibre_29
  · exact center_fibre_30
  · exact center_fibre_31

private theorem centerMask_card_le : Fintype.card {a // centerMask a} ≤ 16 := by
  rw [product_subtype_card_eq_sum centerMask]
  simp_rw [center_fibre_count]
  decide +kernel

theorem center_card_le_sixteen : Nat.card (Subgroup.center Model) ≤ 16 := by
  have hm : ∀ a, centerMask a ↔ ∀ j, ⁅rowEquiv a, generators j⁆ ∈ (⊥ : Subgroup Model) := by
    intro a
    constructor
    · intro h j
      exact model_eq (h j)
    · intro h j
      exact coordinateEq_of_eq (h j)
  have hh := quotientCenterPreimage_card_of_mask (⊥ : Subgroup Model)
    generators generators_full rowEquiv centerMask hm
  have hq := quotientCenter_card_mul (⊥ : Subgroup Model)
  rw [Subgroup.card_bot, mul_one] at hq
  have he := Nat.card_congr
    (RDTDegreeEightExceptionalTransport.centerEquiv
      (QuotientGroup.quotientBot : Model ⧸ (⊥ : Subgroup Model) ≃* Model)).toEquiv
  rw [he] at hq
  rw [hq, hh, Nat.card_eq_fintype_card]
  exact centerMask_card_le

private def lineFibreCount : Fin 3 → Fin 32 → ℕ := ![![8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8],![2,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,2],![2,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,2]]

private theorem line_fibre_0 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,0)} = lineFibreCount l 0 := by
  decide +kernel

private theorem line_fibre_1 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,1)} = lineFibreCount l 1 := by
  decide +kernel

private theorem line_fibre_2 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,2)} = lineFibreCount l 2 := by
  decide +kernel

private theorem line_fibre_3 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,3)} = lineFibreCount l 3 := by
  decide +kernel

private theorem line_fibre_4 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,4)} = lineFibreCount l 4 := by
  decide +kernel

private theorem line_fibre_5 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,5)} = lineFibreCount l 5 := by
  decide +kernel

private theorem line_fibre_6 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,6)} = lineFibreCount l 6 := by
  decide +kernel

private theorem line_fibre_7 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,7)} = lineFibreCount l 7 := by
  decide +kernel

private theorem line_fibre_8 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,8)} = lineFibreCount l 8 := by
  decide +kernel

private theorem line_fibre_9 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,9)} = lineFibreCount l 9 := by
  decide +kernel

private theorem line_fibre_10 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,10)} = lineFibreCount l 10 := by
  decide +kernel

private theorem line_fibre_11 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,11)} = lineFibreCount l 11 := by
  decide +kernel

private theorem line_fibre_12 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,12)} = lineFibreCount l 12 := by
  decide +kernel

private theorem line_fibre_13 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,13)} = lineFibreCount l 13 := by
  decide +kernel

private theorem line_fibre_14 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,14)} = lineFibreCount l 14 := by
  decide +kernel

private theorem line_fibre_15 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,15)} = lineFibreCount l 15 := by
  decide +kernel

private theorem line_fibre_16 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,16)} = lineFibreCount l 16 := by
  decide +kernel

private theorem line_fibre_17 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,17)} = lineFibreCount l 17 := by
  decide +kernel

private theorem line_fibre_18 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,18)} = lineFibreCount l 18 := by
  decide +kernel

private theorem line_fibre_19 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,19)} = lineFibreCount l 19 := by
  decide +kernel

private theorem line_fibre_20 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,20)} = lineFibreCount l 20 := by
  decide +kernel

private theorem line_fibre_21 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,21)} = lineFibreCount l 21 := by
  decide +kernel

private theorem line_fibre_22 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,22)} = lineFibreCount l 22 := by
  decide +kernel

private theorem line_fibre_23 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,23)} = lineFibreCount l 23 := by
  decide +kernel

private theorem line_fibre_24 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,24)} = lineFibreCount l 24 := by
  decide +kernel

private theorem line_fibre_25 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,25)} = lineFibreCount l 25 := by
  decide +kernel

private theorem line_fibre_26 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,26)} = lineFibreCount l 26 := by
  decide +kernel

private theorem line_fibre_27 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,27)} = lineFibreCount l 27 := by
  decide +kernel

private theorem line_fibre_28 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,28)} = lineFibreCount l 28 := by
  decide +kernel

private theorem line_fibre_29 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,29)} = lineFibreCount l 29 := by
  decide +kernel

private theorem line_fibre_30 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,30)} = lineFibreCount l 30 := by
  decide +kernel

private theorem line_fibre_31 : ∀ l : Fin 3,
    Fintype.card {a : KernelIndex // lineCenterMask l (a,31)} = lineFibreCount l 31 := by
  decide +kernel

private theorem line_fibre_count (l : Fin 3) (i : Fin 32) :
    Fintype.card {a : KernelIndex // lineCenterMask l (a,i)} = lineFibreCount l i := by
  fin_cases i
  · exact line_fibre_0 l
  · exact line_fibre_1 l
  · exact line_fibre_2 l
  · exact line_fibre_3 l
  · exact line_fibre_4 l
  · exact line_fibre_5 l
  · exact line_fibre_6 l
  · exact line_fibre_7 l
  · exact line_fibre_8 l
  · exact line_fibre_9 l
  · exact line_fibre_10 l
  · exact line_fibre_11 l
  · exact line_fibre_12 l
  · exact line_fibre_13 l
  · exact line_fibre_14 l
  · exact line_fibre_15 l
  · exact line_fibre_16 l
  · exact line_fibre_17 l
  · exact line_fibre_18 l
  · exact line_fibre_19 l
  · exact line_fibre_20 l
  · exact line_fibre_21 l
  · exact line_fibre_22 l
  · exact line_fibre_23 l
  · exact line_fibre_24 l
  · exact line_fibre_25 l
  · exact line_fibre_26 l
  · exact line_fibre_27 l
  · exact line_fibre_28 l
  · exact line_fibre_29 l
  · exact line_fibre_30 l
  · exact line_fibre_31 l

private theorem lineCenterMask_card_le :
    ∀ l : Fin 3, Fintype.card {a // lineCenterMask l a} ≤ 32 := by
  intro l
  rw [product_subtype_card_eq_sum (lineCenterMask l)]
  simp_rw [line_fibre_count]
  fin_cases l <;> decide +kernel

theorem line_quotient_center_card_le (l : Fin 3) :
    Nat.card (Subgroup.center (Model ⧸ line l)) ≤ 16 := by
  have hm : ∀ a, lineCenterMask l a ↔ ∀ j, ⁅rowEquiv a, generators j⁆ ∈ line l := by
    intro a
    constructor
    · intro h j
      obtain ⟨k, hk⟩ := h j
      exact ⟨k, model_eq hk⟩
    · intro h j
      obtain ⟨k, hk⟩ := h j
      exact ⟨k, coordinateEq_of_eq hk⟩
  have hh := quotientCenterPreimage_card_of_mask (line l)
    generators generators_full rowEquiv (lineCenterMask l) hm
  have hq := quotientCenter_card_mul (line l)
  rw [line_card, hh] at hq
  have hc : Nat.card {a // lineCenterMask l a} ≤ 32 := by
    rw [Nat.card_eq_fintype_card]
    exact lineCenterMask_card_le l
  omega

theorem all_nonabelian_quotients_normalF (N : Subgroup Model) [N.Normal]
    (hnonab : ¬ ∀ a b : Model ⧸ N, a * b = b * a) :
    ∃ F : Subgroup (Model ⧸ N), F.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog F +
        (5 / 4 : ℝ) * MarkedC4.ActualNormalFMarkedPeel.centralLog F ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog F ≤ 4 := by
  apply SmallDerivedCentralLineNormalFBounds.five_quarters_packet
    commutator_card_le_four center_card_le_sixteen ?_ N hnonab
  intro L _ hL hcard
  obtain ⟨l, rfl⟩ := central_line_cases L (hL.trans commutator_le_D) hcard
  exact line_quotient_center_card_le l

end SymmetricSubgroupAsymptotics.BinaryHeisenbergFourCentralLines
