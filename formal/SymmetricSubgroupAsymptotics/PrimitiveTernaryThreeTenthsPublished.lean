import SymmetricSubgroupAsymptotics.PrimitiveCompositionBoundedReceipt
import SymmetricSubgroupAsymptotics.PrimitiveNaturalCompositionZero
import SymmetricSubgroupAsymptotics.PrimitiveCompositionTail
import SymmetricSubgroupAsymptotics.ChiefTernaryOrderBound
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage
import SymmetricSubgroupAsymptotics.PrimitiveTernaryThreeTenthsWeight

/-!
# Primitive three-tenths weight from published classification

Roney-Dougal's classification of primitive permutation groups below degree
2500, represented by the pinned PrimGrp 3.4.4 catalogue, identifies every
primitive action of degree at most 44 with one of the 336 checked rows.  The
ordinary rows need only their exact group order.  The rows whose order
valuation is too large are exactly the natural alternating and symmetric
actions, treated by symbolic composition chains.

Degrees at least 45 use the published Glasby--Praeger--Rosa--Verret
composition-length theorem through `PrimitiveCompositionTail`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The exact bounded information supplied by the published primitive-group
classification.  No ternary weight or numerical inequality is a field. -/
structure PrimitiveCompositionCatalogueMatch
    (G X : Type) [Group G] [Finite G] [Finite X] where
  row : Fin 336
  degree_eq : (primitiveCompositionBoundRow row).degree = Nat.card X
  order_eq : (primitiveCompositionBoundRow row).kind = .orderBound →
    Nat.card G = (primitiveCompositionBoundRow row).groupOrder
  alternating_equiv :
    (primitiveCompositionBoundRow row).kind = .naturalAlternating →
      Nonempty (G ≃* alternatingGroup (Fin (Nat.card X)))
  symmetric_equiv :
    (primitiveCompositionBoundRow row).kind = .naturalSymmetric →
      Nonempty (G ≃* Equiv.Perm (Fin (Nat.card X)))

/-- **Published bounded primitive-catalogue correspondence.**  Every faithful
primitive action of degree below 45 is permutation-isomorphic to one of the
336 PrimGrp 3.4.4 rows.  The match exposes only the row's exact order or its
natural alternating/symmetric identification. -/
def PublishedPrimitiveCompositionCatalogueCorrespondence : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X],
    Nat.card X < 45 → Nonempty (PrimitiveCompositionCatalogueMatch G X)

namespace PrimitiveCompositionCatalogueMatch

variable {G X : Type} [Group G] [Finite G] [Finite X]
  (M : PrimitiveCompositionCatalogueMatch G X)

include M

/-- The complete bounded numerical conclusion.  Ordinary rows use the safe
order-valuation upper bound; natural rows use their symbolic composition
chains. -/
theorem chiefWeight_threeTenths
    (hfour : 4 ≤ Nat.card X) (hnine : Nat.card X ≠ 9)
    (c : ActualChiefSeries G) :
    10 * actualChiefSeriesTernaryWeight c ≤ 3 * Nat.card X := by
  let r := primitiveCompositionBoundRow M.row
  have hrdegree : r.degree = Nat.card X := M.degree_eq
  cases hkind : r.kind with
  | orderBound =>
      have hweight := actualChiefSeriesTernaryWeight_le_order c
      have horder : Nat.card G = r.groupOrder := M.order_eq hkind
      have hvaluation : (Nat.card G).factorization 3 = r.ternaryValuation := by
        rw [horder]
        exact r.valuation_eq
      have hbound : 10 * r.ternaryValuation ≤ 3 * r.degree :=
        r.order_bound hkind (by omega) (by omega)
      omega
  | naturalAlternating =>
      have hnorder : r.kind ≠ .orderBound := by simp [hkind]
      have hfive : 5 ≤ Nat.card X := by
        have := r.natural_degree hnorder
        omega
      obtain ⟨e⟩ := M.alternating_equiv hkind
      have hz := allChiefSeries_zero_of_alternating_equiv
        (Nat.card X) hfive e c
      omega
  | naturalSymmetric =>
      have hnorder : r.kind ≠ .orderBound := by simp [hkind]
      have hfive : 5 ≤ Nat.card X := by
        have := r.natural_degree hnorder
        omega
      obtain ⟨e⟩ := M.symmetric_equiv hkind
      have hz := allChiefSeries_zero_of_symmetric_equiv
        (Nat.card X) hfive e c
      omega

end PrimitiveCompositionCatalogueMatch

/-- The bounded half of the primitive three-tenths theorem. -/
theorem primitiveChiefWeight_threeTenths_bounded_of_published
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hfour : 4 ≤ Nat.card X) (hnine : Nat.card X ≠ 9)
    (hbounded : Nat.card X < 45) (c : ActualChiefSeries G) :
    10 * actualChiefSeriesTernaryWeight c ≤ 3 * Nat.card X := by
  obtain ⟨M⟩ := catalogue G X hbounded
  exact M.chiefWeight_threeTenths hfour hnine c

/-- The full `PrimitiveTernaryThreeTenthsWeightBound`, with only the two
published inputs left: GPRV for the infinite tail and Roney-Dougal/PrimGrp
for the bounded catalogue correspondence. -/
theorem primitiveTernaryThreeTenthsWeightBound_of_published
    (hcomp : PrimitiveCompositionLengthInput)
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence) :
    PrimitiveTernaryThreeTenthsWeightBound := by
  intro G X _ _ _ _ _ _ _ hfour hnine c
  by_cases hlarge : 45 ≤ Nat.card X
  · letI : Fintype X := Fintype.ofFinite X
    have hcard : Fintype.card X = Nat.card X := by
      rw [Nat.card_eq_fintype_card]
    let e : X ≃ Fin (Nat.card X) := (Fintype.equivFin X).trans
      (finCongr hcard)
    let P := labelledActionImage (A := G) e
    let E : G ≃* P := faithfulLabelledActionEquiv e
    let cP : ActualChiefSeries P := actualChiefSeriesComap E.symm c
    have hprimitive : MulAction.IsPreprimitive P (Fin (Nat.card X)) :=
      (labelledAction_preprimitive_iff e).mp (inferInstance)
    have htail := primitiveChiefWeight_strict_tail hcomp (Nat.card X) hlarge
      P hprimitive cP
    have hweight : actualChiefSeriesTernaryWeight cP =
        actualChiefSeriesTernaryWeight c := by
      exact actualChiefSeriesComap_weight E.symm c
    omega
  · exact primitiveChiefWeight_threeTenths_bounded_of_published
      catalogue G X hfour hnine (by omega) c

end SymmetricSubgroupAsymptotics

end
