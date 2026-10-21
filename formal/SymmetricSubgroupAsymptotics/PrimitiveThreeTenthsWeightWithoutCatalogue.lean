import SymmetricSubgroupAsymptotics.PrimitiveAffineSmallTernaryConsumers
import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleSmallTernaryConsumers
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.PrimitiveCompositionTail
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage
import SymmetricSubgroupAsymptotics.PrimitiveTernaryThreeTenthsWeight

/-! The complete primitive three-tenths chief-weight consumer uses the
retained composition-length tail and ordinary simple-index bound. The
bounded part is elementary affine linear counting or actual semisimple
socle projection, with no bounded primitive catalogue premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure

theorem primitiveTernaryThreeTenthsWeightBound_of_linear_and_simpleIndex
    (hcomp : PrimitiveCompositionLengthInput) (hindex : PublishedSimpleIndexBounds) :
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
    | inl D => exact D.small_ternaryChiefWeight_threeTenths hindex (by omega) c
    | inr P =>
        exact P.small_ternaryChiefWeight_threeTenths inferInstance
          (by omega) hfour hnine c

end SymmetricSubgroupAsymptotics
