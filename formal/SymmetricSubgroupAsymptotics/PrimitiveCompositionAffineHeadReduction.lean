import SymmetricSubgroupAsymptotics.PrimitiveCompositionStrictHeadReduction
import SymmetricSubgroupAsymptotics.PrimitiveAffineHeadOrderBudget

/-! The six exceptional degrees in the actual-order strict-head reduction
are also closed in the affine case. No affine representative classification
or socle-quotient row is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private abbrev AffineHeadRowBudget (r : PrimitiveCompositionBoundRow) : Prop :=
  r.kind=.orderBound →
    ((r.degree=9 ∨ r.degree=27) →
      20*r.ternaryValuation<3*r.degree+20*r.degree.factorization 3) ∧
    ((r.degree=11 ∨ r.degree=13) → r.groupOrder≤r.degree^2 →
      20*r.ternaryValuation<3*r.degree)

private theorem first_affine_head_receipt :
    ∀ r∈primitiveCompositionBoundRows2To11.toList,AffineHeadRowBudget r := by
  unfold AffineHeadRowBudget
  rw [List.forall_mem_iff_get]
  decide +kernel
private theorem second_affine_head_receipt :
    ∀ r∈primitiveCompositionBoundRows12To20.toList,AffineHeadRowBudget r := by
  unfold AffineHeadRowBudget
  rw [List.forall_mem_iff_get]
  decide +kernel
private theorem third_affine_head_receipt :
    ∀ r∈primitiveCompositionBoundRows21To27.toList,AffineHeadRowBudget r := by
  unfold AffineHeadRowBudget
  rw [List.forall_mem_iff_get]
  decide +kernel
private theorem fourth_affine_head_receipt :
    ∀ r∈primitiveCompositionBoundRows28To36.toList,AffineHeadRowBudget r := by
  unfold AffineHeadRowBudget
  rw [List.forall_mem_iff_get]
  decide +kernel
private theorem fifth_affine_head_receipt :
    ∀ r∈primitiveCompositionBoundRows37To44.toList,AffineHeadRowBudget r := by
  unfold AffineHeadRowBudget
  rw [List.forall_mem_iff_get]
  decide +kernel

private theorem affine_head_receipt (i : Fin 336) : AffineHeadRowBudget (primitiveCompositionBoundRow i) := by
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
  · exact first_affine_head_receipt _ h
  · exact second_affine_head_receipt _ h
  · exact third_affine_head_receipt _ h
  · exact fourth_affine_head_receipt _ h
  · exact fifth_affine_head_receipt _ h

namespace PrimitiveCompositionCatalogueMatch
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (M : PrimitiveCompositionCatalogueMatch G X)

include M in
theorem affine_strictHead_of_exceptional
    (P : PrimitiveAffineProfile G X)
    (hex : PrimitiveStrictHeadExceptionalDegree (Nat.card X))
    (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)<3*Nat.card X := by
  cases hk : (primitiveCompositionBoundRow M.row).kind with
  | orderBound =>
      have hbudget := affine_head_receipt M.row hk
      have hv : (Nat.card G).factorization 3=(primitiveCompositionBoundRow M.row).ternaryValuation := by
        rw [M.order_eq hk,(primitiveCompositionBoundRow M.row).valuation_eq]
      by_cases hpow : Nat.card X=9 ∨ Nat.card X=27
      · have hh := P.relativeHead_add_degreeFactorization_budget inferInstance 3 (by
          rcases hpow with h|h <;> omega) N
        rw [hv] at hh
        have hn := hbudget.1 (by simpa only [M.degree_eq] using hpow)
        rw [M.degree_eq] at hn
        omega
      by_cases hprime : Nat.card X=11 ∨ Nat.card X=13
      · have hp : (Nat.card X).Prime := by rcases hprime with h|h <;> rw [h] <;> decide
        have hb := P.card_le_degree_sq_of_degree_prime inferInstance hp
        have hn := hbudget.2 (by simpa only [M.degree_eq] using hprime) (by
          rw [←M.order_eq hk,M.degree_eq]
          exact hb)
        have hh := primeRelativeHead_le_groupFactorization 3 N
        rw [hv] at hh
        rw [M.degree_eq] at hn
        omega
      · have hpp := P.degree_isPrimePow inferInstance
        have hc : Nat.card X=10 ∨ Nat.card X=12 := by
          dsimp only [PrimitiveStrictHeadExceptionalDegree] at hex
          omega
        rcases hc with h|h
        · rw [h] at hpp
          exact ((show ¬ IsPrimePow (10 : ℕ) by decide) hpp).elim
        · rw [h] at hpp
          exact ((show ¬ IsPrimePow (12 : ℕ) by decide) hpp).elim
  | naturalAlternating =>
      have hf : 5≤Nat.card X := by
        have h := (primitiveCompositionBoundRow M.row).natural_degree (by simp [hk])
        rwa [M.degree_eq] at h
      obtain ⟨e⟩ := M.alternating_equiv hk
      have hz := allChiefSeries_zero_of_alternating_equiv (Nat.card X) hf e (actualChiefSeries G)
      rw [primeRelativeHead_eq_zero_of_actualChiefWeight_zero N (actualChiefSeries G) hz]
      omega
  | naturalSymmetric =>
      have hf : 5≤Nat.card X := by
        have h := (primitiveCompositionBoundRow M.row).natural_degree (by simp [hk])
        rwa [M.degree_eq] at h
      obtain ⟨e⟩ := M.symmetric_equiv hk
      have hz := allChiefSeries_zero_of_symmetric_equiv (Nat.card X) hf e (actualChiefSeries G)
      rw [primeRelativeHead_eq_zero_of_actualChiefWeight_zero N (actualChiefSeries G) hz]
      omega

end PrimitiveCompositionCatalogueMatch
end SymmetricSubgroupAsymptotics
