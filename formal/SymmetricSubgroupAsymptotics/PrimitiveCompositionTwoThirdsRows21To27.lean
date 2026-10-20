import SymmetricSubgroupAsymptotics.PrimitiveCompositionTwoThirdsPredicate

/-! One bounded-degree chunk of the two-action compression receipt. Only
the literal numerical row fields are reduced by the kernel. -/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 16
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem primitiveTwoThirdsRowReceipt_2_0 :
    ∀ g∈primitiveCompositionBoundRows21To27.toList,
      ∀ t∈primitiveCompositionBoundRows2To11.toList,PrimitiveTwoThirdsRowReceipt g t := by
  unfold PrimitiveTwoThirdsRowReceipt TwoThirdsSolubleSimpleOrder
  simp_rw [List.forall_mem_iff_get]
  decide +kernel

theorem primitiveTwoThirdsRowReceipt_2_1 :
    ∀ g∈primitiveCompositionBoundRows21To27.toList,
      ∀ t∈primitiveCompositionBoundRows12To20.toList,PrimitiveTwoThirdsRowReceipt g t := by
  unfold PrimitiveTwoThirdsRowReceipt TwoThirdsSolubleSimpleOrder
  simp_rw [List.forall_mem_iff_get]
  decide +kernel

theorem primitiveTwoThirdsRowReceipt_2_2 :
    ∀ g∈primitiveCompositionBoundRows21To27.toList,
      ∀ t∈primitiveCompositionBoundRows21To27.toList,PrimitiveTwoThirdsRowReceipt g t := by
  unfold PrimitiveTwoThirdsRowReceipt TwoThirdsSolubleSimpleOrder
  simp_rw [List.forall_mem_iff_get]
  decide +kernel

theorem primitiveTwoThirdsRowReceipt_2_3 :
    ∀ g∈primitiveCompositionBoundRows21To27.toList,
      ∀ t∈primitiveCompositionBoundRows28To36.toList,PrimitiveTwoThirdsRowReceipt g t := by
  unfold PrimitiveTwoThirdsRowReceipt TwoThirdsSolubleSimpleOrder
  simp_rw [List.forall_mem_iff_get]
  decide +kernel

end SymmetricSubgroupAsymptotics
