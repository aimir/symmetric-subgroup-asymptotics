import SymmetricSubgroupAsymptotics.CFSGSufficientPrimitiveTernaryWeights
import SymmetricSubgroupAsymptotics.PrimitiveThreeTenthsWeightWithoutCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveTernaryChiefWeightPublished

/-! The unchanged final primitive chief-weight and three-tenths interfaces
from the sufficient internal simple-index boundary. The large composition
length tail and the actual affine alternatives are exactly the existing
proved consumers; every original chief series is retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure

theorem primitiveTernaryThreeTenthsWeightBound_of_sufficient
    (hcomp : PrimitiveCompositionLengthInput) (hindex : SufficientSimpleIndexBounds) :
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
  · cases Classical.choice (publishedONanScottStructure G X) with
    | inl D => exact D.small_ternaryChiefWeight_threeTenths_of_sufficient hindex (by omega) c
    | inr P =>
        exact P.small_ternaryChiefWeight_threeTenths inferInstance
          (by omega) hfour hnine c


theorem primitiveDegreeNine_chiefWeight_oneThird_of_sufficient
    (hindex : SufficientSimpleIndexBounds)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (h9 : Nat.card X=9) (c : ActualChiefSeries G) :
    3*actualChiefSeriesTernaryWeight c≤Nat.card X := by
  cases Classical.choice (publishedONanScottStructure G X) with
  | inl D =>
      have h := D.small_ternaryChiefWeight_threeTenths_of_sufficient hindex (by omega) c
      omega
  | inr P => exact P.degreeNine_ternaryChiefWeight_oneThird inferInstance h9 c

theorem primitiveTernaryChiefWeightBound_of_sufficient
    (hcomp : PrimitiveCompositionLengthInput) (hindex : SufficientSimpleIndexBounds) :
    PrimitiveTernaryChiefWeightBound (fun r => r/3) := by
  have hWeight := primitiveTernaryThreeTenthsWeightBound_of_sufficient hcomp hindex
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
