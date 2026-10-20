import SymmetricSubgroupAsymptotics.PrimitiveTernaryChiefWeightPublished
import SymmetricSubgroupAsymptotics.PrimitiveTernaryThreeTenthsPublished

/-!
# The degree-nine classification is a slice of the composition catalogue

The degree-nine input used by the ternary chief-weight consumer follows
from the bounded primitive-catalogue correspondence already used by the
three-tenths theorem. Only the degree-nine ordinary orders in the literal
receipt are checked here. The two natural rows retain the group
isomorphisms supplied by that same correspondence.

This is a dependency reduction: the published bounded catalogue
correspondence remains an explicit hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

private theorem degreeNine_order_rows2To11 :
    ∀ r ∈ primitiveCompositionBoundRows2To11.toList,
      r.degree = 9 → r.kind = .orderBound →
        r.groupOrder = 36 ∨ r.groupOrder = 72 ∨ r.groupOrder = 144 ∨
        r.groupOrder = 216 ∨ r.groupOrder = 432 ∨ r.groupOrder = 504 ∨
        r.groupOrder = 1512 := by
  decide +kernel

/-- The ordinary degree-nine orders in the complete typed receipt. Only
the first 56-row chunk requires numerical evaluation; the checked degree
ranges exclude every later chunk. -/
theorem primitiveCompositionBoundRow_degreeNine_order_cases
    (i : Fin 336)
    (hdegree : (primitiveCompositionBoundRow i).degree = 9)
    (hkind : (primitiveCompositionBoundRow i).kind = .orderBound) :
    (primitiveCompositionBoundRow i).groupOrder = 36 ∨
      (primitiveCompositionBoundRow i).groupOrder = 72 ∨
      (primitiveCompositionBoundRow i).groupOrder = 144 ∨
      (primitiveCompositionBoundRow i).groupOrder = 216 ∨
      (primitiveCompositionBoundRow i).groupOrder = 432 ∨
      (primitiveCompositionBoundRow i).groupOrder = 504 ∨
      (primitiveCompositionBoundRow i).groupOrder = 1512 := by
  have hmem : primitiveCompositionBoundRow i ∈ primitiveCompositionBoundRows.toList := by
    unfold primitiveCompositionBoundRow
    exact Array.getElem_mem_toList _
  have hchunks :
      primitiveCompositionBoundRow i ∈ primitiveCompositionBoundRows2To11.toList ∨
      primitiveCompositionBoundRow i ∈ primitiveCompositionBoundRows12To20.toList ∨
      primitiveCompositionBoundRow i ∈ primitiveCompositionBoundRows21To27.toList ∨
      primitiveCompositionBoundRow i ∈ primitiveCompositionBoundRows28To36.toList ∨
      primitiveCompositionBoundRow i ∈ primitiveCompositionBoundRows37To44.toList := by
    simpa only [primitiveCompositionBoundRows, Array.toList_append, List.mem_append,
      or_assoc] using hmem
  rcases hchunks with hm | hm | hm | hm | hm
  · exact degreeNine_order_rows2To11 _ hm hdegree hkind
  · have hrange := primitiveCompositionBoundRows12To20_degree_range _ hm
    omega
  · have hrange := primitiveCompositionBoundRows21To27_degree_range _ hm
    omega
  · have hrange := primitiveCompositionBoundRows28To36_degree_range _ hm
    omega
  · have hrange := primitiveCompositionBoundRows37To44_degree_range _ hm
    omega

/-- The separate degree-nine primitive classification is already supplied
by the broader composition-catalogue correspondence. No additional
classification is assumed. -/
theorem primitiveDegreeNineClassification_of_compositionCatalogue
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence) :
    PublishedPrimitiveDegreeNineClassification := by
  intro G X _ _ _ _ _ _ _ hdegree
  obtain ⟨M⟩ := catalogue G X (by omega)
  cases hkind : (primitiveCompositionBoundRow M.row).kind with
  | orderBound =>
    have hsmall := primitiveCompositionBoundRow_degreeNine_order_cases M.row
      (M.degree_eq.trans hdegree) hkind
    have horder := M.order_eq hkind
    rcases hsmall with h | h | h | h | h | h | h
    · exact Or.inl (horder.trans h)
    · exact Or.inr (Or.inl (horder.trans h))
    · exact Or.inr (Or.inr (Or.inl (horder.trans h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (horder.trans h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (horder.trans h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (horder.trans h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (horder.trans h)))))))
  | naturalAlternating =>
    have he : Nonempty (G ≃* alternatingGroup (Fin 9)) := by
      exact hdegree ▸ M.alternating_equiv hkind
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))))
  | naturalSymmetric =>
    have he : Nonempty (G ≃* Equiv.Perm (Fin 9)) := by
      exact hdegree ▸ M.symmetric_equiv hkind
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr he)))))))

end SymmetricSubgroupAsymptotics

end
