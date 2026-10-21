import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankTenAbelianization
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenElementaryZeroFrame
import SymmetricSubgroupAsymptotics.BinaryElementaryPhiZeroIntrinsicRadical
import SymmetricSubgroupAsymptotics.PGroupRankAdditivityRelativeRadical
import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds
import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule

/-! An original rank-ten source with elementary16 top has its SAME full
pair kernel in the unique11-dimensional original state. Its actual whole
derived subgroup is precisely the5-dimensional original intrinsic
radical. No outer splitting or offset-gauge assumption is required. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance elementaryDerivedModelFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 16))

include F

theorem rank_ten_elementary_original_kernel_model
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hhigh : 10≤MarkedC4.genRank U) (hpow : ∀ t : F.top.range,t^2=1) :
    ∃ E : BinaryPairFrame F.top.range (Fin 8),
      F.top.range=E.splitAffineAction ∧
      E.top.range=BinaryRegularEightNaturalRegistry.H ∧
      E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 23).2.space ∧
      (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
        (BinaryElementary16GraphHeadRigidity.stateChart 0).space ∧
      MarkedC4.genRank U=10 ∧ MarkedC4.normalGen F.top.ker=6 ∧
      MarkedC4.genRank F.top.range=4 := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  letI : Group.IsNilpotent F.top.range := hTop.isNilpotent
  let W : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 16)) :=
    F.axisNaturalSubrepresentation F.top.ker
  have hker : MarkedC4.normalGen F.top.ker=
      Module.finrank (ZMod 2) W.toRepresentation.Coinvariants :=
    F.axisNatural_normalGen F.top.ker le_rfl hU
  have hcap := twoGroup_permutationSubrepresentationHead_le_width hTop 4
    (by norm_num only [Nat.card_fin]) (0 : Fin 16) W
  rw [representationHead_finrank_eq_coinvariants] at hcap
  norm_num [Nat.choose] at hcap
  have hel : BinarySquareActionStructure.SquaresActTrivially
      (G := F.top.range) (X := Fin 16) :=
    BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mpr hpow
  have ht := ElementaryBinaryTransitiveNormalRank.normalGen_le_exponent hel
    (0 : Fin 16) 4 (by norm_num only [Nat.card_fin]) (⊤ : Subgroup F.top.range)
  have htop := (MarkedC4.genRank_le_normalGen_top (G := F.top.range)).trans ht
  letI : IsMulCommutative F.top.ker := ⟨⟨fun a b => F.bitsHom_injective (by
    rw [map_mul,map_mul,mul_comm])⟩⟩
  letI : IsMulCommutative F.top.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  have hg := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    F.top.rangeRestrict F.top.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict] at hg
  have hwide : 6≤Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by omega
  obtain ⟨E₀⟩ := transitiveBinaryPairFrame_nonempty 3 F.top.range hTop
    (by norm_num only [Nat.card_fin])
  obtain ⟨E,hzero,hH,hK⟩ := E₀.exists_original_elementary_zero_frame hTop hpow
  refine ⟨E,hzero,hH,hK,E.elementary_original_zero_graph hzero hH hK W hwide,?_,?_,?_⟩ <;> omega

/-- These premises are supplied together by the original-kernel model
above; the image of the derived subgroup is not independently selected. -/
theorem elementary_rank_ten_derived_coordinate_radical
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hpow : ∀ t : F.top.range,t^2=1)
    (E : BinaryPairFrame F.top.range (Fin 8))
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=BinaryRegularEightNaturalRegistry.H)
    (hK : E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 23).2.space)
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
        (BinaryElementary16GraphHeadRigidity.stateChart 0).space)
    (hgen : MarkedC4.genRank U=10) (hker : MarkedC4.normalGen F.top.ker=6)
    (htop : MarkedC4.genRank F.top.range=4) :
    commutator U≤F.top.ker ∧
      (F.ambientAxis (commutator U)).map E.originalCoordinateEquiv.toLinearMap=
        BinaryElementaryPhiZeroIntrinsicRadical.radical.space ∧
      Nat.card (commutator U)=32 := by
  let beta := F.top.rangeRestrict
  have hbeta : Function.Surjective beta := F.top.rangeRestrict_surjective
  have hk : beta.ker=F.top.ker := MonoidHom.ker_rangeRestrict F.top
  have hdegree : Nat.card X=32 := by simpa only [Nat.card_fin] using F.card_points
  have hexp := binary_degree_thirty_two_rank_ten_abelianization_exponent U hU hdegree hgen
  have hpowker (k : beta.ker) : (k : U)^2=1 := by
    let a : F.top.ker := ⟨k,by rw [←hk];exact k.property⟩
    have ha : a^2=1 := by
      apply F.kernelChart.injective
      rw [map_pow,map_one]
      change (2 : ℕ) • (F.kernelChart a).toAdd=0
      exact ZModModule.char_nsmul_eq_zero 2 _
    exact congrArg Subtype.val ha
  have hrank : MarkedC4.genRank U=MarkedC4.normalGen beta.ker+MarkedC4.genRank F.top.range := by
    rw [hk,hgen,hker,htop]
  have hRbeta := pGroup_relativeRadical_eq_inf_commutator_of_rank_additivity
    2 hU beta hbeta hpowker hexp hrank
  have htransport (K : Subgroup U) [K.Normal] (he : beta.ker=K) :
      primeRelativeRadical 2 K=K ⊓ commutator U := by
    subst K
    exact hRbeta
  have hR := htransport F.top.ker hk
  letI : IsMulCommutative F.top.range := ⟨⟨fun a b =>
    (Commute.of_orderOf_dvd_two
      (fun t => orderOf_dvd_iff_pow_eq_one.mpr (hpow t)) a b).eq⟩⟩
  have hm : (commutator U).map beta=⊥ := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hbeta]
    exact commutator_eq_bot F.top.range
  have hd : commutator U≤F.top.ker := by
    rw [←hk]
    exact Subgroup.map_le_iff_le_comap.mp (le_of_eq hm)
  rw [inf_eq_right.mpr hd] at hR
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants≤6 := by
    rw [←F.axisNatural_normalGen F.top.ker le_rfl hU,hker]
  have hcoord : (F.ambientAxis (commutator U)).map E.originalCoordinateEquiv.toLinearMap=
      BinaryElementaryPhiZeroIntrinsicRadical.radical.space := by
    rw [←hR,F.axisNatural_radical F.top.ker le_rfl]
    exact BinaryElementaryPhiZeroIntrinsicRadical.original_radical_eq E hzero hH hK W hS hcap
  have haxis : Nat.card (F.ambientAxis (commutator U))=Nat.card (commutator U) := by
    have hc := F.coordinateSubgroup_card (F.ambientAxis (commutator U))
      (F.ambientAxis_le_kernelSpace (commutator U))
    rw [F.coordinateSubgroup_ambientAxis,inf_eq_right.mpr hd] at hc
    exact hc.symm
  have hmapcard : Nat.card (F.ambientAxis (commutator U))=
      Nat.card (BinaryElementaryPhiZeroIntrinsicRadical.radical.space) := by
    have he : Nat.card (F.ambientAxis (commutator U))=
        Nat.card ((F.ambientAxis (commutator U)).map E.originalCoordinateEquiv.toLinearMap) :=
      Nat.card_congr (Submodule.equivMapOfInjective E.originalCoordinateEquiv.toLinearMap
        E.originalCoordinateEquiv.injective (F.ambientAxis (commutator U))).toEquiv
    exact he.trans (congrArg
      (fun A : Submodule (ZMod 2) (Fin 16 → ZMod 2) => Nat.card A) hcoord)
  have hradcard : Nat.card (BinaryElementaryPhiZeroIntrinsicRadical.radical.space)=32 :=
    (BinaryCoordinateSpace.card BinaryElementaryPhiZeroIntrinsicRadical.radical).trans
      (by norm_num)
  have hdcard : Nat.card (commutator U)=32 :=
    (haxis.symm.trans hmapcard).trans hradcard
  exact ⟨hd,hcoord,hdcard⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
