import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialComplete
import Mathlib.Data.Finset.Sort

/-! Three actual incomparable labels are covered by the sparse certificate.
Only a three-element subset of the retained leading antichain is selected. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial

theorem antichain_contains_labels (s : Finset (Fin 16))
    (hs : IsAntichain TopRel (s : Set (Fin 16))) (hcard : 3 ≤ s.card) :
    ∃ c : Fin 36, ∀ k : Fin 3, labels c k ∈ s := by
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hcard
  let v : Fin 3 ↪o Fin 16 := t.orderEmbOfFin ht
  have hm (i : Fin 3) : v i ∈ s := hts (t.orderEmbOfFin_mem ht i)
  have h01 : v 0 < v 1 := v.strictMono (by decide)
  have h12 : v 1 < v 2 := v.strictMono (by decide)
  have h02 : v 0 < v 2 := lt_trans h01 h12
  obtain ⟨c, hc0, hc1, hc2⟩ := sorted_triple_coverage (v 0) (v 1) (v 2) h01 h12
    (hs (hm 0) (hm 1) (ne_of_lt h01))
    (hs (hm 1) (hm 0) (ne_of_gt h01))
    (hs (hm 0) (hm 2) (ne_of_lt h02))
    (hs (hm 2) (hm 0) (ne_of_gt h02))
    (hs (hm 1) (hm 2) (ne_of_lt h12))
    (hs (hm 2) (hm 1) (ne_of_gt h12))
  refine ⟨c, ?_⟩
  intro k
  fin_cases k
  · change labels c 0 ∈ s
    rw [hc0]
    exact hm 0
  · change labels c 1 ∈ s
    rw [hc1]
    exact hm 1
  · change labels c 2 ∈ s
    rw [hc2]
    exact hm 2

end SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomial
