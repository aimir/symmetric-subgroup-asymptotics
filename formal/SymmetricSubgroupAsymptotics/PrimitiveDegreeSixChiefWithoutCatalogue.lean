import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import SymmetricSubgroupAsymptotics.ChiefSeriesTransport

/-! Zero ternary chief weight follows from the actual simple full socle
and its quotient of order at most two. No abstract primitive model is
chosen. Point relabelling only transports the resulting actual chief
chain back to the original group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure

namespace PrimitiveDegreeSixActualNormalConsumers

/-- An original chain has either the one nonabelian simple step or that
step followed by the actual quotient of order two. -/
theorem exists_zero_chiefSeries
    {G : Type} [Group G] [Finite G] [MulAction G (Fin 6)] [FaithfulSMul G (Fin 6)]
    [MulAction.IsPreprimitive G (Fin 6)] (hindex : PublishedSimpleIndexBounds) :
    ∃ c : ActualChiefSeries G,actualChiefSeriesTernaryWeight c=0 := by
  let D := nonaffineData (G := G)
  let S := finiteGroupSocle G
  let e : S≃*D.Simple := D.oneFactorEquiv (D.degreeSix_factorCount_one hindex)
  letI : IsSimpleGroup S := e.isSimpleGroup
  have hnc : ¬IsMulCommutative S := by
    intro hs
    apply D.noncommutative
    apply IsMulCommutative.of_comm
    intro a b
    have hh := congrArg e (hs.is_comm.comm (e.symm a) (e.symm b))
    simpa only [map_mul,e.apply_symm_apply] using hh
  have hi : S.index≤2 := by
    simpa only [S,Subgroup.index_eq_card] using socle_quotient_card_le_two (G := G) hindex
  have hp : 0<S.index := by rw [S.index_eq_card];exact Nat.card_pos
  by_cases hone : S.index=1
  · have ht : S=⊤ := Subgroup.index_eq_one.mp hone
    let eS : G≃*S := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr ht.symm)
    exact ⟨actualChiefSeriesComap eS (simpleChiefSeries S),
      (actualChiefSeriesComap_weight eS (simpleChiefSeries S)).trans (simpleChiefSeries_weight S hnc)⟩
  · have htwo : S.index=2 := by omega
    exact ⟨indexTwoSimpleChiefSeries S htwo,indexTwoSimpleChiefSeries_weight S htwo hnc⟩

end PrimitiveDegreeSixActualNormalConsumers

/-- The degree18 imprimitive consumer needs this actual zero-weight
series, rather than the stronger four-model classification. -/
theorem primitiveDegreeSix_chiefWeight_zero_without_catalogue
    (hindex : PublishedSimpleIndexBounds)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hX : Nat.card X=6) :
    ∃ c : ActualChiefSeries G,actualChiefSeriesTernaryWeight c=0 := by
  let points : X≃Fin 6 := Finite.equivFinOfCardEq hX
  let S := labelledActionImage (A := G) points
  letI : MulAction.IsPreprimitive S (Fin 6) :=
    (labelledAction_preprimitive_iff points).mp inferInstance
  let e : G≃*S := faithfulLabelledActionEquiv points
  obtain ⟨c,hc⟩ := PrimitiveDegreeSixActualNormalConsumers.exists_zero_chiefSeries (G := S) hindex
  exact ⟨actualChiefSeriesComap e c,(actualChiefSeriesComap_weight e c).trans hc⟩

end SymmetricSubgroupAsymptotics
