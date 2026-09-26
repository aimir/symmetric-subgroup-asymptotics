import SymmetricSubgroupAsymptotics.ChiefCompositionTernaryCount
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! A finite certificate interface for actual composition chains. Each
step is a proper normal inclusion with a simple quotient; displayed
factor orders must be proved equal to the actual relative indices.
The proved index Jordan–Hölder theorem converts these witnesses into
bounds for every chosen chief series. Numeric records alone do not
inhabit either certificate structure. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G]

/-- An ascending actual subgroup chain, from the trivial subgroup to the
original ambient group. `step` includes strictness and maximal normality.
Use `ofNormalSimple` to supply literal normal/simple quotient evidence. -/
structure FiniteCompositionWitness (G : Type) [Group G] where
  length : ℕ
  subgroup : Fin (length + 1) → Subgroup G
  head : subgroup 0 = ⊥
  last : subgroup (Fin.last length) = ⊤
  step : ∀ i : Fin length,
    NormalCompositionCover (subgroup i.castSucc) (subgroup i.succ)

namespace FiniteCompositionWitness

/-- The quotient hypotheses are about the actual consecutive subgroups,
with the lower subgroup normal inside the actual upper subgroup. -/
def ofNormalSimple (l : ℕ) (K : Fin (l + 1) → Subgroup G)
    (h0 : K 0 = ⊥) (hl : K (Fin.last l) = ⊤)
    (hlt : ∀ i : Fin l, K i.castSucc < K i.succ)
    (hn : ∀ i : Fin l, ((K i.castSucc).subgroupOf (K i.succ)).Normal)
    (hs : ∀ i : Fin l, letI := hn i
      IsSimpleGroup (K i.succ ⧸ (K i.castSucc).subgroupOf (K i.succ))) :
    FiniteCompositionWitness G where
  length := l
  subgroup := K
  head := h0
  last := hl
  step i := by
    letI := hn i
    letI := hs i
    exact NormalCompositionCover.of_simple (hlt i)

/-- For soluble chain certificates, prime actual relative indices already
imply simplicity of the actual quotients. No separate simple-group
classification or quotient multiplication table is required. -/
def ofPrimeIndices (l : ℕ) (K : Fin (l + 1) → Subgroup G)
    (h0 : K 0 = ⊥) (hl : K (Fin.last l) = ⊤)
    (hlt : ∀ i : Fin l, K i.castSucc < K i.succ)
    (hn : ∀ i : Fin l, ((K i.castSucc).subgroupOf (K i.succ)).Normal)
    (hp : ∀ i : Fin l, ((K i.castSucc).relIndex (K i.succ)).Prime) :
    FiniteCompositionWitness G := by
  apply ofNormalSimple l K h0 hl hlt hn
  intro i
  letI := hn i
  letI : Fact (((K i.castSucc).relIndex (K i.succ)).Prime) := ⟨hp i⟩
  exact isSimpleGroup_of_prime_card
    (p := (K i.castSucc).relIndex (K i.succ)) (by
      simp only [Subgroup.relIndex, Subgroup.index_eq_card])

/-- The same literal chain in the proved relative-index Jordan–Hölder
lattice. No ambient normality of intermediate subgroups is required. -/
def asIndexSeries (W : FiniteCompositionWitness G) :
    @CompositionSeries (Subgroup G) inferInstance (subgroupIndexJordanHolder G) where
  length := W.length
  toFun := W.subgroup
  step := W.step

/-- Count edges by their actual quotient orders, not by the valuation of
the ambient group order. -/
def orderCount (W : FiniteCompositionWitness G) (p : ℕ) : ℕ :=
  ∑ i : Fin W.length,
    if (W.subgroup i.castSucc).relIndex (W.subgroup i.succ) = p then 1 else 0

theorem edge_order_equiv (W : FiniteCompositionWitness G)
    (t : SubnormalCompositionSeries G) :
    ∃ e : Fin t.chain.length ≃ Fin W.length, ∀ i,
      (t.chain i.castSucc).val.relIndex (t.chain i.succ).val =
        (W.subgroup (e i).castSucc).relIndex (W.subgroup (e i).succ) := by
  letI := subgroupIndexJordanHolder G
  have hh : (subnormalCompositionAsIndexSeries t).head = W.asIndexSeries.head :=
    t.head.trans W.head.symm
  have hl : (subnormalCompositionAsIndexSeries t).last = W.asIndexSeries.last :=
    t.last.trans W.last.symm
  exact CompositionSeries.jordan_holder (subnormalCompositionAsIndexSeries t)
    W.asIndexSeries hh hl

theorem orderCount_eq (W : FiniteCompositionWitness G)
    (p : ℕ) (t : SubnormalCompositionSeries G) :
    compositionOrderCount p t = W.orderCount p := by
  obtain ⟨e, he⟩ := W.edge_order_equiv t
  apply Fintype.sum_equiv e
  intro i
  rw [he i]

/-- Every chosen chief series is bounded by this supplied actual chain. -/
theorem chiefWeight_le [Finite G] (W : FiniteCompositionWitness G)
    (c : ActualChiefSeries G) :
    actualChiefSeriesTernaryWeight c ≤ W.orderCount 3 := by
  obtain ⟨t, _, _, _, _⟩ := actualChiefSeries_composition_refinement c
  exact (actualChiefWeight_le_composition_ternary_count c t).trans_eq
    (W.orderCount_eq 3 t)

theorem exists_chiefSeries_le [Finite G] (W : FiniteCompositionWitness G) :
    ∃ c : ActualChiefSeries G, actualChiefSeriesTernaryWeight c ≤ W.orderCount 3 :=
  ⟨actualChiefSeries G, W.chiefWeight_le (actualChiefSeries G)⟩

end FiniteCompositionWitness

/-- Displayed factor orders carry exact bindings to the actual subgroup
chain. A bound on their order-three count can then be a small arithmetic
certificate, separate from the group-theoretic certificates. -/
structure FiniteCompositionOrderCertificate (G : Type) [Group G] where
  witness : FiniteCompositionWitness G
  edgeOrder : Fin witness.length → ℕ
  edgeOrder_eq : ∀ i,
    (witness.subgroup i.castSucc).relIndex (witness.subgroup i.succ) = edgeOrder i

namespace FiniteCompositionOrderCertificate

/-- Quotient-cardinality certificates can be supplied directly. They
must use the original lower and upper subgroups of each witnessed edge. -/
def ofQuotientOrders (W : FiniteCompositionWitness G)
    (q : Fin W.length → ℕ)
    (hq : ∀ i : Fin W.length, letI := (W.step i).normal
      Nat.card (W.subgroup i.succ ⧸
        (W.subgroup i.castSucc).subgroupOf (W.subgroup i.succ)) = q i) :
    FiniteCompositionOrderCertificate G where
  witness := W
  edgeOrder := q
  edgeOrder_eq i := by
    letI := (W.step i).normal
    simpa only [Subgroup.relIndex, Subgroup.index_eq_card] using hq i

def count (C : FiniteCompositionOrderCertificate G) (p : ℕ) : ℕ :=
  ∑ i : Fin C.witness.length, if C.edgeOrder i = p then 1 else 0

theorem count_eq (C : FiniteCompositionOrderCertificate G) (p : ℕ) :
    C.count p = C.witness.orderCount p := by
  apply Finset.sum_congr rfl
  intro i _
  rw [C.edgeOrder_eq i]

theorem chiefWeight_le [Finite G] (C : FiniteCompositionOrderCertificate G)
    (c : ActualChiefSeries G) :
    actualChiefSeriesTernaryWeight c ≤ C.count 3 :=
  (C.witness.chiefWeight_le c).trans_eq (C.count_eq 3).symm

theorem chiefWeight_le_of_count_le [Finite G]
    (C : FiniteCompositionOrderCertificate G) (c : ActualChiefSeries G)
    (b : ℕ) (hb : C.count 3 ≤ b) :
    actualChiefSeriesTernaryWeight c ≤ b := (C.chiefWeight_le c).trans hb

theorem exists_chiefSeries_le [Finite G] (C : FiniteCompositionOrderCertificate G) :
    ∃ c : ActualChiefSeries G, actualChiefSeriesTernaryWeight c ≤ C.count 3 :=
  ⟨actualChiefSeries G, C.chiefWeight_le (actualChiefSeries G)⟩

end FiniteCompositionOrderCertificate
end SymmetricSubgroupAsymptotics
