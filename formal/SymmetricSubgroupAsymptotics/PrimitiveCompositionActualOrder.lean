import SymmetricSubgroupAsymptotics.PrimitiveTernaryThreeTenthsPublished
import Mathlib.GroupTheory.Perm.Finite

/-! All three kinds of the retained composition match have their literal
row order. Natural rows are transported using their actual group isomorphism
and the factorial cardinality formula; no order-only recognition is inferred. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private abbrev NaturalOrderReceipt (r : PrimitiveCompositionBoundRow) : Prop :=
  (r.kind=.naturalAlternating → r.groupOrder=r.degree.factorial/2) ∧
  (r.kind=.naturalSymmetric → r.groupOrder=r.degree.factorial)

private theorem natural_order_receipt_0 :
    ∀ r∈primitiveCompositionBoundRows2To11.toList,NaturalOrderReceipt r := by
  unfold NaturalOrderReceipt
  rw [List.forall_mem_iff_get]
  decide +kernel
private theorem natural_order_receipt_1 :
    ∀ r∈primitiveCompositionBoundRows12To20.toList,NaturalOrderReceipt r := by
  unfold NaturalOrderReceipt
  rw [List.forall_mem_iff_get]
  decide +kernel
private theorem natural_order_receipt_2 :
    ∀ r∈primitiveCompositionBoundRows21To27.toList,NaturalOrderReceipt r := by
  unfold NaturalOrderReceipt
  rw [List.forall_mem_iff_get]
  decide +kernel
private theorem natural_order_receipt_3 :
    ∀ r∈primitiveCompositionBoundRows28To36.toList,NaturalOrderReceipt r := by
  unfold NaturalOrderReceipt
  rw [List.forall_mem_iff_get]
  decide +kernel
private theorem natural_order_receipt_4 :
    ∀ r∈primitiveCompositionBoundRows37To44.toList,NaturalOrderReceipt r := by
  unfold NaturalOrderReceipt
  rw [List.forall_mem_iff_get]
  decide +kernel

private theorem natural_order_receipt (i : Fin 336) :
    NaturalOrderReceipt (primitiveCompositionBoundRow i) := by
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
  · exact natural_order_receipt_0 _ h
  · exact natural_order_receipt_1 _ h
  · exact natural_order_receipt_2 _ h
  · exact natural_order_receipt_3 _ h
  · exact natural_order_receipt_4 _ h

namespace PrimitiveCompositionCatalogueMatch
variable {G X : Type} [Group G] [Finite G] [Finite X]
    (M : PrimitiveCompositionCatalogueMatch G X)

/-- Literal order equality for every matched row kind, using the supplied
actual natural-action isomorphism in the alternating/symmetric branches. -/
theorem card_eq_row : Nat.card G=(primitiveCompositionBoundRow M.row).groupOrder := by
  cases hk : (primitiveCompositionBoundRow M.row).kind with
  | orderBound => exact M.order_eq hk
  | naturalAlternating =>
      have hf : 5≤Nat.card X := by
        have h := (primitiveCompositionBoundRow M.row).natural_degree (by simp [hk])
        rwa [M.degree_eq] at h
      letI : Nontrivial (Fin (Nat.card X)) := Fin.nontrivial_iff_two_le.mpr (by omega)
      obtain ⟨e⟩ := M.alternating_equiv hk
      rw [(natural_order_receipt M.row).1 hk,M.degree_eq]
      have hc := Nat.card_congr e.toEquiv
      rw [nat_card_alternatingGroup,Nat.card_fin] at hc
      exact hc
  | naturalSymmetric =>
      obtain ⟨e⟩ := M.symmetric_equiv hk
      rw [(natural_order_receipt M.row).2 hk,M.degree_eq]
      have hc := Nat.card_congr e.toEquiv
      rw [Nat.card_perm,Nat.card_fin] at hc
      exact hc

end PrimitiveCompositionCatalogueMatch
end SymmetricSubgroupAsymptotics
