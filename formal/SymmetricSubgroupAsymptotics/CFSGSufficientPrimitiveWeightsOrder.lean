import SymmetricSubgroupAsymptotics.CFSGPrimitiveChiefWeightTail
import SymmetricSubgroupAsymptotics.CFSGSufficientPrimitiveWeights

/-! The SAME original primitive chief-weight interfaces, proved without
primitive composition length. The bounded small consumers are unchanged;
all larger degrees use the actual full-socle/affine order tail. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure

theorem primitiveTernaryThreeTenthsWeightBound_of_sufficientOrder
    (hindex : SufficientSimpleIndexBounds) : PrimitiveTernaryThreeTenthsWeightBound := by
  intro G X _ _ _ _ _ _ _ hfour hnine c
  by_cases hlarge : 45 ≤ Nat.card X
  · exact primitiveChiefThreeTenths_tail_of_sufficient hindex (G := G) (X := X) hlarge c
  · cases Classical.choice (publishedONanScottStructure G X) with
    | inl D => exact D.small_ternaryChiefWeight_threeTenths_of_sufficient hindex (by omega) c
    | inr P =>
        exact P.small_ternaryChiefWeight_threeTenths inferInstance
          (by omega) hfour hnine c

theorem primitiveTernaryChiefWeightBound_of_sufficientOrder
    (hindex : SufficientSimpleIndexBounds) :
    PrimitiveTernaryChiefWeightBound (fun r => r/3) := by
  have hWeight := primitiveTernaryThreeTenthsWeightBound_of_sufficientOrder hindex
  intro G X _ _ _ _ _ _ _
  let r := Nat.card X
  by_cases hr9 : r=9
  · let c := actualChiefSeries G
    have h := primitiveDegreeNine_chiefWeight_oneThird_of_sufficient hindex
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
