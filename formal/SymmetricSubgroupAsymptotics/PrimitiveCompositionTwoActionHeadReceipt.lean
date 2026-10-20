import SymmetricSubgroupAsymptotics.PrimitiveCompositionActualOrder

/-! A shared two-action arithmetic receipt. The original primitive action
and the simple socle's actual least-index primitive action are both located
by the same composition correspondence. Exact order factorization and
transitivity, rather than a separate socle locator, close the small head
budgets. -/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 16
noncomputable section
namespace SymmetricSubgroupAsymptotics

abbrev PrimitiveSmallSocleHeadDegree (n : ℕ) : Prop :=
  n=6 ∨ n=9 ∨ n=10 ∨ n=11 ∨ n=12 ∨ n=13 ∨ n=18

private abbrev CrossHeadReceipt (g t : PrimitiveCompositionBoundRow) : Prop :=
  ∀ q : Fin 15,0<q.val → g.kind=.orderBound →
    PrimitiveSmallSocleHeadDegree g.degree → 5≤t.degree → t.degree≤g.degree →
    q.val*t.groupOrder=g.groupOrder → g.degree∣t.groupOrder →
      (g.degree≠18 → 20*q.val.factorization 3<3*g.degree) ∧
      (g.degree=18 → q.val.factorization 3=0)

private theorem cross_head_0_0 :
    ∀ g∈primitiveCompositionBoundRows2To11.toList,
      ∀ t∈primitiveCompositionBoundRows2To11.toList,CrossHeadReceipt g t := by
  unfold CrossHeadReceipt PrimitiveSmallSocleHeadDegree
  simp_rw [List.forall_mem_iff_get]
  decide +kernel
private theorem cross_head_0_1 :
    ∀ g∈primitiveCompositionBoundRows2To11.toList,
      ∀ t∈primitiveCompositionBoundRows12To20.toList,CrossHeadReceipt g t := by
  unfold CrossHeadReceipt PrimitiveSmallSocleHeadDegree
  simp_rw [List.forall_mem_iff_get]
  decide +kernel
private theorem cross_head_1_0 :
    ∀ g∈primitiveCompositionBoundRows12To20.toList,
      ∀ t∈primitiveCompositionBoundRows2To11.toList,CrossHeadReceipt g t := by
  unfold CrossHeadReceipt PrimitiveSmallSocleHeadDegree
  simp_rw [List.forall_mem_iff_get]
  decide +kernel
private theorem cross_head_1_1 :
    ∀ g∈primitiveCompositionBoundRows12To20.toList,
      ∀ t∈primitiveCompositionBoundRows12To20.toList,CrossHeadReceipt g t := by
  unfold CrossHeadReceipt PrimitiveSmallSocleHeadDegree
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

/-- Two actual order matches suffice for the entire small ternary-head
budget. Neither match is a numerical head or socle-quotient assumption. -/
theorem primitiveComposition_twoAction_smallHead_receipt
    (i j : Fin 336) (q : ℕ) (hq0 : 0<q) (hq : q<15)
    (hg : (primitiveCompositionBoundRow i).kind=.orderBound)
    (hn : PrimitiveSmallSocleHeadDegree (primitiveCompositionBoundRow i).degree)
    (hell : 5≤(primitiveCompositionBoundRow j).degree)
    (hle : (primitiveCompositionBoundRow j).degree≤(primitiveCompositionBoundRow i).degree)
    (horder : q*(primitiveCompositionBoundRow j).groupOrder=(primitiveCompositionBoundRow i).groupOrder)
    (hdegree : (primitiveCompositionBoundRow i).degree∣(primitiveCompositionBoundRow j).groupOrder) :
    ((primitiveCompositionBoundRow i).degree≠18 →
      20*q.factorization 3<3*(primitiveCompositionBoundRow i).degree) ∧
    ((primitiveCompositionBoundRow i).degree=18 → q.factorization 3=0) := by
  have hi : (primitiveCompositionBoundRow i).degree≤18 := by
    dsimp only [PrimitiveSmallSocleHeadDegree] at hn
    omega
  have hj : (primitiveCompositionBoundRow j).degree≤18 := by omega
  rcases row_mem_low i hi with hi|hi <;> rcases row_mem_low j hj with hj|hj
  · exact cross_head_0_0 _ hi _ hj ⟨q,hq⟩ hq0 hg hn hell hle horder hdegree
  · exact cross_head_0_1 _ hi _ hj ⟨q,hq⟩ hq0 hg hn hell hle horder hdegree
  · exact cross_head_1_0 _ hi _ hj ⟨q,hq⟩ hq0 hg hn hell hle horder hdegree
  · exact cross_head_1_1 _ hi _ hj ⟨q,hq⟩ hq0 hg hn hell hle horder hdegree

end SymmetricSubgroupAsymptotics
