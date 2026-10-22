import SymmetricSubgroupAsymptotics.CFSGSufficientSixPointConsumers
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixChiefWithoutCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveDegreeEighteenHeadWithoutCatalogue

/-! Actual six-point zero chief series and primitive18 head at most two.
All uses of the sharp outer logarithm are below27; the unchanged quantified
order-square estimate supplies the actual simple full socle. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

theorem NonaffineData.oneFactor_quotient_lt_fifteen_of_sufficient_degree_lt_twentySeven
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hk : D.factorCount = 1)
    (hindex : SufficientSimpleIndexBounds) (hs : Nat.card X < 27) :
    Nat.card (G ⧸ finiteGroupSocle G) < 15 := by
  obtain ⟨ell, _, hf, hd, hb⟩ :=
    D.oneFactor_sharp_log_of_sufficient_degree_lt_twentySeven hk hindex hs
  exact quotient_order_lt_fifteen_of_log (by omega) (by omega) hb

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure


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
theorem exists_zero_chiefSeries_of_sufficient
    {G : Type} [Group G] [Finite G] [MulAction G (Fin 6)] [FaithfulSMul G (Fin 6)]
    [MulAction.IsPreprimitive G (Fin 6)] (hindex : SufficientSimpleIndexBounds) :
    ∃ c : ActualChiefSeries G,actualChiefSeriesTernaryWeight c=0 := by
  let D := nonaffineData_of_sufficient (G := G)
  let S := finiteGroupSocle G
  let e : S≃*D.Simple := D.oneFactorEquiv (D.degreeSix_factorCount_one_of_sufficient hindex)
  letI : IsSimpleGroup S := e.isSimpleGroup
  have hnc : ¬IsMulCommutative S := by
    intro hs
    apply D.noncommutative
    apply IsMulCommutative.of_comm
    intro a b
    have hh := congrArg e (hs.is_comm.comm (e.symm a) (e.symm b))
    simpa only [map_mul,e.apply_symm_apply] using hh
  have hi : S.index≤2 := by
    simpa only [S,Subgroup.index_eq_card] using socle_quotient_card_le_two_of_sufficient (G := G) hindex
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
theorem primitiveDegreeSix_chiefWeight_zero_of_sufficient
    (hindex : SufficientSimpleIndexBounds)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hX : Nat.card X=6) :
    ∃ c : ActualChiefSeries G,actualChiefSeriesTernaryWeight c=0 := by
  let points : X≃Fin 6 := Finite.equivFinOfCardEq hX
  let S := labelledActionImage (A := G) points
  letI : MulAction.IsPreprimitive S (Fin 6) :=
    (labelledAction_preprimitive_iff points).mp inferInstance
  let e : G≃*S := faithfulLabelledActionEquiv points
  obtain ⟨c,hc⟩ := PrimitiveDegreeSixActualNormalConsumers.exists_zero_chiefSeries_of_sufficient (G := S) hindex
  exact ⟨actualChiefSeriesComap e c,(actualChiefSeriesComap_weight e c).trans hc⟩

end SymmetricSubgroupAsymptotics


/-! The primitive degree18 consumer needs head at most two, rather than
an exact vanishing statement. Its actual outer quotient has order below15
by the ordinary retained simple-index bound, which suffices directly. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure

private theorem eighteen_not_two_power (d : ℕ) : 18≠2^d := by
  intro h
  by_cases hd : d<5
  · interval_cases d <;> norm_num at h
  · have h5 : 5≤d := by omega
    have h32 : (32 : ℕ)≤2^d := pow_le_pow_right₀ (by decide : (1 : ℕ)≤2) h5
    omega

theorem primitive_degreeEighteen_ternaryHead_le_two_of_sufficient
    (hindex : SufficientSimpleIndexBounds)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hX : Nat.card X=18) (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)≤2 := by
  cases Classical.choice (publishedONanScottStructure G X) with
  | inl D =>
      obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
      have hf : 5≤ell := nonabelianSimple_leastProperIndex_five_le
        (fun hc => D.noncommutative (isMulCommutative_iff.mpr hc)) hell.1
      have horder := (hindex D.Simple D.noncommutative ell hell).1
      have hd := primitiveSocle_power_le_degree hf horder (D.degreeForm hell)
      rw [hX] at hd
      have hk : D.factorCount=1 := by
        by_contra h
        have hk2 : 2≤D.factorCount := by have hp:=D.factorCount_pos;omega
        have h25 : 25≤ell^D.factorCount := calc
          25=5^2 := by decide
          _ ≤ ell^2 := Nat.pow_le_pow_left hf 2
          _ ≤ ell^D.factorCount := pow_le_pow_right₀ (by omega : 1≤ell) hk2
        omega
      letI : Group.IsPerfect D.Simple := simple_perfect_of_nonabelian D.noncommutative
      letI : Group.IsPerfect (finiteGroupSocle G) :=
        Group.IsPerfect.ofSurjective (f := (D.oneFactorEquiv hk).symm.toMonoidHom)
          (D.oneFactorEquiv hk).symm.surjective
      have hh := primeRelativeHead_le_quotientFactorization_of_perfect_unique
        3 (finiteGroupSocle G) (D.oneFactor_socle_le hk) N
      have hb := ternaryValuation_le_two_of_lt_fifteen _
        (D.oneFactor_quotient_lt_fifteen_of_sufficient_degree_lt_twentySeven hk hindex (by omega))
      omega
  | inr P =>
      let x : X := Classical.choice inferInstance
      letI : Fact P.p.Prime := ⟨P.p_prime⟩
      obtain ⟨d,hd⟩ := P.V_pgroup.exists_card_eq
      have he : 18=P.p^d := hX.symm.trans ((P.card_eq x).symm.trans hd)
      have hp : P.p=2 := by
        rcases P.p_prime.eq_two_or_odd' with hp|hp
        · exact hp
        · have ho : Odd 18 := he.symm ▸ hp.pow
          exact ((by decide : ¬Odd 18) ho).elim
      rw [hp] at he
      exact (eighteen_not_two_power d he).elim

end SymmetricSubgroupAsymptotics
