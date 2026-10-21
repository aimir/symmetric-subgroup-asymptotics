import SymmetricSubgroupAsymptotics.BinarySixteenRankSixIntegralNormals
import SymmetricSubgroupAsymptotics.BinaryPairRankSixIntegralSaturation
import SymmetricSubgroupAsymptotics.RelativeIntegralCyclicQuotient
import SymmetricSubgroupAsymptotics.ElementaryBinaryTransitiveNormalRank

/-! The rank-six actual sixteen-point top needs no new integral census.
Its independently proved normal-F packet controls proper top images of
index at least four. At top index two, equality in the integral lift is
excluded by the checked original-axis mixed-radical engines. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance rankSixTopIntegralFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) [MulAction.IsPretransitive U X]
include F

omit F [MulAction.IsPretransitive U X] in
private theorem integral_is_power_two (hU : IsPGroup 2 U) (N : Subgroup U) [N.Normal] :
    ∃ k : ℕ,normalIntegralCoinvariantOrder N=2^k := by
  obtain ⟨n,hn⟩ := (hU.to_subgroup N).exists_card_eq
  have hd : normalIntegralCoinvariantOrder N∣2^n := by
    rw [←hn]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact ⟨k,hk⟩

/-- Full integral bound for every SAME original normal of index greater
than two; no ordinary normal-generator lower bound is assumed. -/
theorem rank_six_top_large_index_normal_integral_order_le_two_fifty_six
    (hU : IsPGroup 2 U) (hTopRank : 6≤MarkedC4.genRank F.top.range)
    (hAb : Nat.card (Abelianization U)≤1024)
    (N : Subgroup U) [N.Normal] (hlarge : 2<N.index) :
    normalIntegralCoinvariantOrder N≤256 := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  letI : Group.IsNilpotent F.top.range := hTop.isNilpotent
  obtain ⟨E⟩ := transitiveBinaryPairFrame_nonempty 3 F.top.range hTop
    (by norm_num only [Nat.card_fin])
  let f := F.top.rangeRestrict
  have hf : Function.Surjective f := F.top.rangeRestrict_surjective
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hpowers : ∀ k : f.ker,(k : U)^2=1 := by
    intro k
    exact F.kernel_square ⟨k.val,by simpa only [f,MonoidHom.ker_rangeRestrict] using k.property⟩
  by_cases hfull : N.map f=⊤
  · letI : IsMulCommutative F.top.ker := ⟨⟨fun a b => F.bitsHom_injective (by
      rw [map_mul,map_mul,mul_comm])⟩⟩
    have hsup : N⊔F.top.ker=⊤ := by
      have hh := congrArg (Subgroup.comap f) hfull
      simpa only [Subgroup.comap_map_eq,Subgroup.comap_top,f,MonoidHom.ker_rangeRestrict] using hh
    have he := relative_integral_order_mul_index_of_abelian_supplement N F.top.ker hsup
    change normalIntegralCoinvariantOrder N*N.index=Nat.card (Abelianization U) at he
    have hi : 4≤N.index := by
      by_contra hh
      have hthree : N.index=3 := by omega
      obtain ⟨n,hncard⟩ := hU.exists_card_eq
      have hd := N.index_dvd_card
      rw [hthree,hncard] at hd
      have hbad := Nat.prime_three.dvd_of_dvd_pow hd
      norm_num at hbad
    have hm : normalIntegralCoinvariantOrder N*4≤1024 :=
      (Nat.mul_le_mul_left _ hi).trans (he.le.trans hAb)
    omega
  have hTopAb : Nat.card (Abelianization F.top.range)≤64 := by
    simpa only [Nat.card_fin] using twoGroup_transitive_abelianization_card_le_quarter_add_two F.top.range hTop
  have hindexTwoOrFour : (N.map f).index=2 ∨ 4≤(N.map f).index := by
    have hlo := (N.map f).one_lt_index_of_ne_top hfull
    by_cases he : (N.map f).index=2
    · exact Or.inl he
    · right
      by_contra hn
      have hthree : (N.map f).index=3 := by omega
      obtain ⟨n,hncard⟩ := hTop.exists_card_eq
      have hd := (N.map f).index_dvd_card
      rw [hthree,hncard] at hd
      have hbad := Nat.prime_three.dvd_of_dvd_pow hd
      norm_num at hbad
  have hTint : normalIntegralCoinvariantOrder (N.map f)≤32 := by
    rcases hindexTwoOrFour with hi | hi
    · letI : IsCyclic (F.top.range ⧸ N.map f) :=
        isCyclic_of_prime_card (p := 2) (by exact hi)
      have he := relative_integral_order_mul_index_of_cyclic_quotient (N.map f)
      change normalIntegralCoinvariantOrder (N.map f)*(N.map f).index=
        Nat.card (Abelianization F.top.range) at he
      rw [hi] at he
      omega
    · exact (E.sixteen_rank_six_large_index_normal_integral_order_le_sixteen hTop hTopRank (N.map f) hi).trans (by decide)
  have hnon : ¬∀ t : F.top.range,t^2=1 := by
    intro hel
    have hs : BinarySquareActionStructure.SquaresActTrivially (G := F.top.range) (X := Fin 16) :=
      BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mpr hel
    have hh := ElementaryBinaryTransitiveNormalRank.normalGen_le_exponent hs (0 : Fin 16) 4
      (by norm_num only [Nat.card_fin]) (⊤ : Subgroup F.top.range)
    have hg := MarkedC4.genRank_le_normalGen_top (G := F.top.range)
    omega
  have hA : MarkedC4.normalGen (N⊓F.top.ker)≤4 := by
    let W := F.axisNaturalSubrepresentation (N⊓F.top.ker)
    have hh := twoGroup_faithful_permutationSubrepresentationHead_le_quarter hTop hnon W
    rw [representationHead_finrank_eq_coinvariants,
      ←F.axisNatural_normalGen (N⊓F.top.ker) inf_le_right hU] at hh
    norm_num only [Nat.card_fin] at hh
    exact hh
  have hb : normalIntegralCoinvariantOrder N≤
      2^MarkedC4.normalGen (N⊓F.top.ker)*normalIntegralCoinvariantOrder (N.map f) := by
    simpa only [f,MonoidHom.ker_rangeRestrict] using
      normalIntegralCoinvariantOrder_le_elementary_kernel 2 hU f hf hpowers N
  have hmax : normalIntegralCoinvariantOrder N≤512 :=
    hb.trans ((Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0<2) hA) hTint).trans (by decide))
  by_contra hbad
  have hlo : 256<normalIntegralCoinvariantOrder N := by omega
  obtain ⟨k,hk⟩ := integral_is_power_two hU N
  have hkhi : k≤9 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (by simpa only [←hk] using hmax)
  have hklo : 8<k := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (by simpa only [←hk] using hlo)
  have hNexact : normalIntegralCoinvariantOrder N=512 := by rw [hk,show k=9 by omega];norm_num
  have hAexact : MarkedC4.normalGen (N⊓F.top.ker)=4 := by
    by_contra hn
    have ha3 : MarkedC4.normalGen (N⊓F.top.ker)≤3 := by omega
    have hm := hb.trans (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0<2) ha3) hTint)
    norm_num [hNexact] at hm
  have hTlarge : 16<normalIntegralCoinvariantOrder (N.map f) := by
    rw [hAexact,hNexact] at hb
    norm_num at hb
    omega
  have hi : (N.map f).index=2 := by
    rcases hindexTwoOrFour with hi | hi
    · exact hi
    · have hh := E.sixteen_rank_six_large_index_normal_integral_order_le_sixteen hTop hTopRank (N.map f) hi
      omega
  have hTexact : normalIntegralCoinvariantOrder (N.map f)=32 := by
    rw [hAexact,hNexact] at hb
    norm_num at hb
    omega
  have hsat : normalIntegralCoinvariantOrder N=
      2^MarkedC4.normalGen (N⊓F.top.ker)*normalIntegralCoinvariantOrder (N.map F.top.rangeRestrict) := by
    change normalIntegralCoinvariantOrder N=
      2^MarkedC4.normalGen (N⊓F.top.ker)*normalIntegralCoinvariantOrder (N.map f)
    rw [hNexact,hAexact,hTexact]
    norm_num
  have hindex := F.rank_six_four_axis_integral_saturation_index_two hU hTopRank N hAexact hi hsat
  omega
end SymmetricSubgroupAsymptotics.BinaryPairFrame
