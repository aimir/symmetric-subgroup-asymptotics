import SymmetricSubgroupAsymptotics.SubgroupIndexJordanHolder
import SymmetricSubgroupAsymptotics.SubnormalCompositionRefinement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Orders of simple factors in original composition series are matched
by a proved Jordan–Hölder equivalence. In particular the number of
factors of order three is independent of the chosen actual series. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G]

def subnormalCompositionAsIndexSeries (t : SubnormalCompositionSeries G) :
    @CompositionSeries (Subgroup G) inferInstance (subgroupIndexJordanHolder G) where
  length := t.chain.length
  toFun i := (t.chain i).val
  step i := by
    obtain ⟨hn, _, hm⟩ := subnormalCover_maximal_normal
      (t.chain i.castSucc) (t.chain i.succ) (t.chain.step i)
    exact ⟨(t.chain.step i).lt, hn, hm⟩

theorem compositionSeries_edge_order_equiv (s t : SubnormalCompositionSeries G) :
    ∃ e : Fin s.chain.length ≃ Fin t.chain.length, ∀ i,
      (s.chain i.castSucc).val.relIndex (s.chain i.succ).val =
        (t.chain (e i).castSucc).val.relIndex (t.chain (e i).succ).val := by
  letI := subgroupIndexJordanHolder G
  have hh : (subnormalCompositionAsIndexSeries s).head =
      (subnormalCompositionAsIndexSeries t).head := s.head.trans t.head.symm
  have hl : (subnormalCompositionAsIndexSeries s).last =
      (subnormalCompositionAsIndexSeries t).last := s.last.trans t.last.symm
  exact CompositionSeries.jordan_holder (subnormalCompositionAsIndexSeries s)
    (subnormalCompositionAsIndexSeries t) hh hl

/-- Count actual simple composition edges with the displayed order. -/
def compositionOrderCount (p : ℕ) (t : SubnormalCompositionSeries G) : ℕ :=
  ∑ i : Fin t.chain.length,
    if (t.chain i.castSucc).val.relIndex (t.chain i.succ).val = p then 1 else 0

theorem compositionOrderCount_eq (p : ℕ) (s t : SubnormalCompositionSeries G) :
    compositionOrderCount p s = compositionOrderCount p t := by
  obtain ⟨e, he⟩ := compositionSeries_edge_order_equiv s t
  apply Fintype.sum_equiv e
  intro i
  rw [he i]

end SymmetricSubgroupAsymptotics
