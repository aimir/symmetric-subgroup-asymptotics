import SymmetricSubgroupAsymptotics.PrimitiveThreeTenthsWeightWithoutCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveTernaryChiefWeightPublished

/-! The actual degree9 one-third chief consumer follows from linear order
counting in its affine alternative and the generic socle-quotient bound in
its nonaffine alternative. No degree9 row classification is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure

theorem primitiveDegreeNine_chiefWeight_oneThird_without_catalogue
    (hindex : PublishedSimpleIndexBounds)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (h9 : Nat.card X=9) (c : ActualChiefSeries G) :
    3*actualChiefSeriesTernaryWeight c≤Nat.card X := by
  cases Classical.choice (publishedONanScottStructure G X) with
  | inl D =>
      have h := D.small_ternaryChiefWeight_threeTenths hindex (by omega) c
      omega
  | inr P => exact P.degreeNine_ternaryChiefWeight_oneThird inferInstance h9 c

theorem primitiveTernaryChiefWeightBound_without_catalogue
    (hcomp : PrimitiveCompositionLengthInput) (hindex : PublishedSimpleIndexBounds) :
    PrimitiveTernaryChiefWeightBound (fun r => r/3) := by
  have hWeight := primitiveTernaryThreeTenthsWeightBound_of_linear_and_simpleIndex hcomp hindex
  intro G X _ _ _ _ _ _ _
  let r := Nat.card X
  by_cases hr9 : r=9
  · let c := actualChiefSeries G
    have h := primitiveDegreeNine_chiefWeight_oneThird_without_catalogue hindex
      (by simpa only [r] using hr9) c
    refine ⟨c,(Nat.le_div_iff_mul_le (by decide : 0<3)).mpr ?_⟩
    omega
  by_cases hr4 : 4 ≤ r
  · let c := actualChiefSeries G
    have hw : 10 * actualChiefSeriesTernaryWeight c ≤ 3 * r :=
      hWeight G X (by simpa only [r] using hr4) (by simpa only [r] using hr9) c
    refine ⟨c, (Nat.le_div_iff_mul_le (by omega : 0 < 3)).mpr ?_⟩
    omega
  · let e : X ≃ Fin r := Finite.equivFin X
    let P := labelledActionImage (A := G) e
    let cP := actualChiefSeries P
    let c := faithfulLabelledActionChiefSeries e cP
    have hr : 2 ≤ r := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hcP : actualChiefSeriesTernaryWeight cP ≤ r / 3 := by
      by_cases hr2 : r ≤ 2
      · have hz := permutationChiefWeight_eq_zero_of_card_le_two P cP (by
          simpa only [Nat.card_fin] using hr2)
        omega
      · have ho := permutationChiefWeight_le_one_of_card_le_five P cP (by
          simp only [Nat.card_fin]
          omega)
        omega
    exact ⟨c, by
      rw [show actualChiefSeriesTernaryWeight c =
          actualChiefSeriesTernaryWeight cP from
        faithfulLabelledActionChiefSeries_weight e cP]
      exact hcP⟩

end SymmetricSubgroupAsymptotics
