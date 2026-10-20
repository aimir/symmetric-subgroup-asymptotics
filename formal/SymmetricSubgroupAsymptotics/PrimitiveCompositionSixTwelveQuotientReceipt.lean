import SymmetricSubgroupAsymptotics.PrimitiveCompositionActualOrder

/-! Exact arithmetic for degree6/12 unique-simple-socle consumers. The sole
residual pair is a simple factor of order1320 in its degree12 action. -/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 16
noncomputable section
namespace SymmetricSubgroupAsymptotics

private abbrev SixTwelveReceipt (g t : PrimitiveCompositionBoundRow) : Prop :=
  ∀ q : Fin 15,0<q.val → g.kind=.orderBound → (g.degree=6 ∨ g.degree=12) →
    5≤t.degree → t.degree≤g.degree →
    q.val*t.groupOrder=g.groupOrder → g.degree∣t.groupOrder →
    2^q.val≤t.degree^3 → q.val≤2 ∨ (t.degree=12 ∧ t.groupOrder=1320)

private theorem six_twelve_0_0 :
    ∀ g∈primitiveCompositionBoundRows2To11.toList,
      ∀ t∈primitiveCompositionBoundRows2To11.toList,SixTwelveReceipt g t := by
  unfold SixTwelveReceipt
  simp_rw [List.forall_mem_iff_get]
  decide +kernel

private theorem six_twelve_0_1 :
    ∀ g∈primitiveCompositionBoundRows2To11.toList,
      ∀ t∈primitiveCompositionBoundRows12To20.toList,SixTwelveReceipt g t := by
  unfold SixTwelveReceipt
  simp_rw [List.forall_mem_iff_get]
  decide +kernel

private theorem six_twelve_1_0 :
    ∀ g∈primitiveCompositionBoundRows12To20.toList,
      ∀ t∈primitiveCompositionBoundRows2To11.toList,SixTwelveReceipt g t := by
  unfold SixTwelveReceipt
  simp_rw [List.forall_mem_iff_get]
  decide +kernel

private theorem six_twelve_1_1 :
    ∀ g∈primitiveCompositionBoundRows12To20.toList,
      ∀ t∈primitiveCompositionBoundRows12To20.toList,SixTwelveReceipt g t := by
  unfold SixTwelveReceipt
  simp_rw [List.forall_mem_iff_get]
  decide +kernel

private theorem row_mem_low (i : Fin 336) (h : (primitiveCompositionBoundRow i).degree≤18) :
    primitiveCompositionBoundRow i∈primitiveCompositionBoundRows2To11.toList ∨
    primitiveCompositionBoundRow i∈primitiveCompositionBoundRows12To20.toList := by
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
  · exact Or.inr h
  · have hh := primitiveCompositionBoundRows21To27_degree_range _ h
    omega
  · have hh := primitiveCompositionBoundRows28To36_degree_range _ h
    omega
  · have hh := primitiveCompositionBoundRows37To44_degree_range _ h
    omega

theorem primitiveComposition_twoAction_sixTwelve_receipt
    (i j : Fin 336) (q : ℕ) (hq0 : 0<q) (hq : q<15)
    (hg : (primitiveCompositionBoundRow i).kind=.orderBound)
    (hn : (primitiveCompositionBoundRow i).degree=6 ∨ (primitiveCompositionBoundRow i).degree=12)
    (hell : 5≤(primitiveCompositionBoundRow j).degree)
    (hle : (primitiveCompositionBoundRow j).degree≤(primitiveCompositionBoundRow i).degree)
    (horder : q*(primitiveCompositionBoundRow j).groupOrder=(primitiveCompositionBoundRow i).groupOrder)
    (hdegree : (primitiveCompositionBoundRow i).degree∣(primitiveCompositionBoundRow j).groupOrder)
    (hlog : 2^q≤(primitiveCompositionBoundRow j).degree^3) :
    q≤2 ∨ ((primitiveCompositionBoundRow j).degree=12 ∧
      (primitiveCompositionBoundRow j).groupOrder=1320) := by
  have hi : (primitiveCompositionBoundRow i).degree≤18 := by omega
  have hj : (primitiveCompositionBoundRow j).degree≤18 := by omega
  rcases row_mem_low i hi with hi|hi <;> rcases row_mem_low j hj with hj|hj
  · exact six_twelve_0_0 _ hi _ hj ⟨q,hq⟩ hq0 hg hn hell hle horder hdegree hlog
  · exact six_twelve_0_1 _ hi _ hj ⟨q,hq⟩ hq0 hg hn hell hle horder hdegree hlog
  · exact six_twelve_1_0 _ hi _ hj ⟨q,hq⟩ hq0 hg hn hell hle horder hdegree hlog
  · exact six_twelve_1_1 _ hi _ hj ⟨q,hq⟩ hq0 hg hn hell hle horder hdegree hlog

/-- Every actual degree6 composition row has order divisible by five. -/
theorem primitiveComposition_degreeSix_five_dvd (i : Fin 336)
    (hi : (primitiveCompositionBoundRow i).degree=6) :
    5∣(primitiveCompositionBoundRow i).groupOrder := by
  have h := row_mem_low i (by omega)
  rcases h with h|h
  · have hr : ∀ r∈primitiveCompositionBoundRows2To11.toList,
        r.degree=6 → 5∣r.groupOrder := by
      rw [List.forall_mem_iff_get]
      decide +kernel
    exact hr _ h hi
  · have hh := primitiveCompositionBoundRows12To20_degree_range _ h
    omega

end SymmetricSubgroupAsymptotics
