import SymmetricSubgroupAsymptotics.BinaryBooleanFourLargeQuadraticSet

/-! Four quadratic leading supports cover every linear or constant
support. Actual downward-leading operators therefore supply the smaller
shears even when the original top lifts have triangular errors. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
open BinaryElementaryPairMonomialWidth

private theorem small_support_avoiders_card : ∀ a : Fin 16,
    (support a).card ≤ 1 →
      (quadraticMasks.filter (fun b => ¬support a ⊆ support b)).card ≤ 3 := by decide

theorem every_small_support_covered_by_four_quadratics
    (Q : Finset (Fin 16)) (hQ : ∀ b ∈ Q, (support b).card = 2)
    (hcard : 4 ≤ Q.card) (a : Fin 16) (ha : (support a).card ≤ 1) :
    ∃ b ∈ Q, support a ⊆ support b := by
  classical
  by_contra hnone
  have hsub : Q ⊆ quadraticMasks.filter (fun b => ¬support a ⊆ support b) := by
    intro b hb
    apply Finset.mem_filter.mpr
    refine ⟨(mem_quadraticMasks_iff b).mpr (hQ b hb), ?_⟩
    intro hab
    exact hnone ⟨b, hb, hab⟩
  have hc := (Finset.card_le_card hsub).trans (small_support_avoiders_card a ha)
  omega

theorem four_quadratic_leading_vectors_give_small_supports
    (K : Submodule (ZMod 2) V)
    (hdownward : ∀ a b : Fin 16, support b ⊆ support a →
      (∃ f ∈ K, FiniteRowLeadingWeight.HasLeading f a) →
        ∃ f ∈ K, FiniteRowLeadingWeight.HasLeading f b)
    (Q : Finset (Fin 16)) (hQ : ∀ b ∈ Q, (support b).card = 2) (hcard : 4 ≤ Q.card)
    (hactual : ∀ b ∈ Q, ∃ f ∈ K, FiniteRowLeadingWeight.HasLeading f b) :
    ∀ a : Fin 16, (support a).card ≤ 1 → ∃ f ∈ K, FiniteRowLeadingWeight.HasLeading f a := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := every_small_support_covered_by_four_quadratics Q hQ hcard a ha
  exact hdownward b a hab (hactual b hb)

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
