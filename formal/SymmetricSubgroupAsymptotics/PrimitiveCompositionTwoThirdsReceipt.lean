import SymmetricSubgroupAsymptotics.PrimitiveCompositionTwoThirdsRows2To11
import SymmetricSubgroupAsymptotics.PrimitiveCompositionTwoThirdsRows12To20
import SymmetricSubgroupAsymptotics.PrimitiveCompositionTwoThirdsRows21To27
import SymmetricSubgroupAsymptotics.PrimitiveCompositionTwoThirdsRows28To36

/-! Assembly of split finite two-action receipts. Every use below concerns
the matched original action and the matched actual simple least-index action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem row_mem_under_thirty (i : Fin 336)
    (h : (primitiveCompositionBoundRow i).degree<30) :
    primitiveCompositionBoundRow i∈primitiveCompositionBoundRows2To11.toList ∨
    primitiveCompositionBoundRow i∈primitiveCompositionBoundRows12To20.toList ∨
    primitiveCompositionBoundRow i∈primitiveCompositionBoundRows21To27.toList ∨
    primitiveCompositionBoundRow i∈primitiveCompositionBoundRows28To36.toList := by
  have hm : primitiveCompositionBoundRow i∈primitiveCompositionBoundRows.toList := by
    unfold primitiveCompositionBoundRow
    exact Array.getElem_mem_toList _
  have hc :
    primitiveCompositionBoundRow i∈primitiveCompositionBoundRows2To11.toList ∨
    primitiveCompositionBoundRow i∈primitiveCompositionBoundRows12To20.toList ∨
    primitiveCompositionBoundRow i∈primitiveCompositionBoundRows21To27.toList ∨
    primitiveCompositionBoundRow i∈primitiveCompositionBoundRows28To36.toList ∨
    primitiveCompositionBoundRow i∈primitiveCompositionBoundRows37To44.toList := by
    simpa only [primitiveCompositionBoundRows,Array.toList_append,List.mem_append,or_assoc] using hm
  rcases hc with h|h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · have hh := primitiveCompositionBoundRows37To44_degree_range _ h
    omega

/-- The complete finite ratio receipt with only the actual binary action
exceptions and impossible soluble simple-order candidates left explicit. -/
theorem primitiveComposition_twoAction_twoThirds_receipt
    (i j : Fin 336) :
    PrimitiveTwoThirdsRowReceipt (primitiveCompositionBoundRow i) (primitiveCompositionBoundRow j) := by
  intro q hq hg hf hs ht hle ho hd hp
  have hj : (primitiveCompositionBoundRow j).degree<30 := by omega
  rcases row_mem_under_thirty i hs with hi|hi|hi|hi <;>
    rcases row_mem_under_thirty j hj with hj|hj|hj|hj
  · exact primitiveTwoThirdsRowReceipt_0_0 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_0_1 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_0_2 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_0_3 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_1_0 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_1_1 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_1_2 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_1_3 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_2_0 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_2_1 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_2_2 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_2_3 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_3_0 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_3_1 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_3_2 _ hi _ hj q hq hg hf hs ht hle ho hd hp
  · exact primitiveTwoThirdsRowReceipt_3_3 _ hi _ hj q hq hg hf hs ht hle ho hd hp

end SymmetricSubgroupAsymptotics
