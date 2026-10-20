import SymmetricSubgroupAsymptotics.PrimitiveTernaryThreeTenthsPublished
import SymmetricSubgroupAsymptotics.PrimitiveRelativeHeadOrderBudgets
import SymmetricSubgroupAsymptotics.OriginalNormalChiefHead

/-! Almost every bounded strict-head consumer follows from the already
retained actual-order correspondence alone. The remaining six degrees are
isolated semantically, without adding a second per-row correspondence. -/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 16
noncomputable section
namespace SymmetricSubgroupAsymptotics

abbrev PrimitiveStrictHeadExceptionalDegree (r : ℕ) : Prop :=
  r=9 ∨ r=10 ∨ r=11 ∨ r=12 ∨ r=13 ∨ r=27

private theorem first_strict_receipt :
    ∀ r∈primitiveCompositionBoundRows2To11.toList,
      r.kind=.orderBound → r.degree<34 → r.degree≠3 → r.degree≠4 →
      r.degree≠6 → r.degree≠18 → PrimitiveStrictHeadExceptionalDegree r.degree ∨
      20*r.ternaryValuation<3*r.degree := by
  unfold PrimitiveStrictHeadExceptionalDegree
  rw [List.forall_mem_iff_get]
  decide +kernel
private theorem second_strict_receipt :
    ∀ r∈primitiveCompositionBoundRows12To20.toList,
      r.kind=.orderBound → r.degree<34 → r.degree≠3 → r.degree≠4 →
      r.degree≠6 → r.degree≠18 → PrimitiveStrictHeadExceptionalDegree r.degree ∨
      20*r.ternaryValuation<3*r.degree := by
  unfold PrimitiveStrictHeadExceptionalDegree
  rw [List.forall_mem_iff_get]
  decide +kernel
private theorem third_strict_receipt :
    ∀ r∈primitiveCompositionBoundRows21To27.toList,
      r.kind=.orderBound → r.degree<34 → r.degree≠3 → r.degree≠4 →
      r.degree≠6 → r.degree≠18 → PrimitiveStrictHeadExceptionalDegree r.degree ∨
      20*r.ternaryValuation<3*r.degree := by
  unfold PrimitiveStrictHeadExceptionalDegree
  rw [List.forall_mem_iff_get]
  decide +kernel
private theorem fourth_strict_receipt :
    ∀ r∈primitiveCompositionBoundRows28To36.toList,
      r.kind=.orderBound → r.degree<34 → r.degree≠3 → r.degree≠4 →
      r.degree≠6 → r.degree≠18 → PrimitiveStrictHeadExceptionalDegree r.degree ∨
      20*r.ternaryValuation<3*r.degree := by
  unfold PrimitiveStrictHeadExceptionalDegree
  rw [List.forall_mem_iff_get]
  decide +kernel

theorem primitiveCompositionBoundRow_strictHead_or_exceptional
    (i : Fin 336) (hk : (primitiveCompositionBoundRow i).kind=.orderBound)
    (hs : (primitiveCompositionBoundRow i).degree<34)
    (h3 : (primitiveCompositionBoundRow i).degree≠3)
    (h4 : (primitiveCompositionBoundRow i).degree≠4)
    (h6 : (primitiveCompositionBoundRow i).degree≠6)
    (h18 : (primitiveCompositionBoundRow i).degree≠18) :
    PrimitiveStrictHeadExceptionalDegree (primitiveCompositionBoundRow i).degree ∨
      20*(primitiveCompositionBoundRow i).ternaryValuation<3*(primitiveCompositionBoundRow i).degree := by
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
  · exact first_strict_receipt _ h hk hs h3 h4 h6 h18
  · exact second_strict_receipt _ h hk hs h3 h4 h6 h18
  · exact third_strict_receipt _ h hk hs h3 h4 h6 h18
  · exact fourth_strict_receipt _ h hk hs h3 h4 h6 h18
  · have hr := primitiveCompositionBoundRows37To44_degree_range _ h
    omega

namespace PrimitiveCompositionCatalogueMatch
variable {G X : Type} [Group G] [Finite G] [Finite X]
    (M : PrimitiveCompositionCatalogueMatch G X)

include M in
theorem strictHead_or_exceptional
    (hs : Nat.card X<34) (h3 : Nat.card X≠3) (h4 : Nat.card X≠4)
    (h6 : Nat.card X≠6) (h18 : Nat.card X≠18) (N : Subgroup G) [N.Normal] :
    PrimitiveStrictHeadExceptionalDegree (Nat.card X) ∨
      20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)<3*Nat.card X := by
  cases hk : (primitiveCompositionBoundRow M.row).kind with
  | orderBound =>
      have hc := primitiveCompositionBoundRow_strictHead_or_exceptional M.row hk
        (by rwa [M.degree_eq]) (by rwa [M.degree_eq]) (by rwa [M.degree_eq])
        (by rwa [M.degree_eq]) (by rwa [M.degree_eq])
      rcases hc with he|hb
      · exact Or.inl (M.degree_eq ▸ he)
      · right
        have hh := primeRelativeHead_le_groupFactorization 3 N
        have hv : (Nat.card G).factorization 3=(primitiveCompositionBoundRow M.row).ternaryValuation := by
          rw [M.order_eq hk,(primitiveCompositionBoundRow M.row).valuation_eq]
        rw [hv] at hh
        rw [M.degree_eq] at hb
        omega
  | naturalAlternating =>
      have hf : 5≤Nat.card X := by
        have h := (primitiveCompositionBoundRow M.row).natural_degree (by simp [hk])
        rwa [M.degree_eq] at h
      obtain ⟨e⟩ := M.alternating_equiv hk
      have hz := allChiefSeries_zero_of_alternating_equiv (Nat.card X) hf e (actualChiefSeries G)
      have hh := primeRelativeHead_eq_zero_of_actualChiefWeight_zero N (actualChiefSeries G) hz
      right
      rw [hh]
      omega
  | naturalSymmetric =>
      have hf : 5≤Nat.card X := by
        have h := (primitiveCompositionBoundRow M.row).natural_degree (by simp [hk])
        rwa [M.degree_eq] at h
      obtain ⟨e⟩ := M.symmetric_equiv hk
      have hz := allChiefSeries_zero_of_symmetric_equiv (Nat.card X) hf e (actualChiefSeries G)
      have hh := primeRelativeHead_eq_zero_of_actualChiefWeight_zero N (actualChiefSeries G) hz
      right
      rw [hh]
      omega

end PrimitiveCompositionCatalogueMatch
end SymmetricSubgroupAsymptotics
