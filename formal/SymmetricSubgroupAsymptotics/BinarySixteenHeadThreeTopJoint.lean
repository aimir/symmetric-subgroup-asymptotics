import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenHighRankTopModels
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerModelBound
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel12
import SymmetricSubgroupAsymptotics.BinarySixteenRankSixIntegralNormals
import SymmetricSubgroupAsymptotics.SmallDerivedNormalFBounds
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard
import SymmetricSubgroupAsymptotics.PGroupGeneratorAbelianizationOrder

/-! Rank-six sixteen-point tops which admit an actual head-three natural
submodule have order at most1024 and derived order at most16. The unique
larger inner model is excluded by its checked head-two capacity. Every
literal normal quotient consequently has derived-times-center at most256.
No affine lift is assumed split. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance headThreeTopJointPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (E : BinaryPairFrame U (Fin 8))
include E

theorem sixteen_rank_six_head_three_source_card_le_1024
    (hU : IsPGroup 2 U) (hrank : 6≤MarkedC4.genRank U)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hhead : 3≤Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    Nat.card U≤1024 := by
  have hbound (Q : BinaryPairFrame U (Fin 8))
      (hK : Nat.card Q.kernelSpace≤128) (hH : Nat.card Q.top.range≤8) : Nat.card U≤1024 := by
    have hh := Q.kernelSpace_card_mul_top
    nlinarith [Nat.mul_le_mul hK hH]
  rcases E.six_le_genRank_literal_top_models hU hrank with
    ⟨g,hH,hlarge⟩ | ⟨g,hH,hlarge⟩
  · let Q := E.reindex g
    rcases Q.regular_large_axis_models hU Q.top.ker le_rfl hH
        (by change 3≤MarkedC4.normalGen Q.top.ker at hlarge;omega) with
      ⟨hK,_⟩ | ⟨hK,_⟩
    all_goals rw [Q.ambientAxis_kernel] at hK
    · apply hbound Q
      · rw [hK,←BinaryRegularEightNaturalRegistry.kernel45_space,
          BinaryRegularEightNaturalRegistry.states_space]
        exact (BinaryRegularEightNaturalRegistry.charts 45).2.card.le
      · rw [hH,BinaryMenuCayley8T3.exact_card]
    · apply hbound Q
      · rw [hK,←BinaryRegularEightNaturalRegistry.kernel46_space,
          BinaryRegularEightNaturalRegistry.states_space]
        exact (BinaryRegularEightNaturalRegistry.charts 46).2.card.le.trans (by decide)
      · rw [hH,BinaryMenuCayley8T3.exact_card]
  · let Q := E.reindex g
    rcases Q.heisenberg_large_axis_models hU Q.top.ker le_rfl hH
        (by change 2≤MarkedC4.normalGen Q.top.ker at hlarge;omega) with
      ⟨hK,_⟩ | ⟨hK,_⟩ | ⟨hK,_⟩
    all_goals rw [Q.ambientAxis_kernel] at hK
    · have hchart : Q.kernelSpace=(BinaryHeisenbergEightNaturalHeads.charts 12).2.space := by
        rw [←BinaryHeisenbergEightNaturalHeads.states_space,
          BinaryHeisenbergEightNaturalHeads.kernel12_space]
        exact hK
      have hb := Q.naturalModuleHead_le_of_literal_pair_layer_bound
        BinaryHeisenbergEightNaturalHeads.H hH _ hchart 2
        BinaryPairLayerHead8T22Kernel12.pair_bound W
      omega
    · have hk : Nat.card Q.kernelSpace≤32 := by
        rw [hK,←BinaryHeisenbergEightNaturalHeads.kernel13_space,
          BinaryHeisenbergEightNaturalHeads.states_space]
        exact (BinaryHeisenbergEightNaturalHeads.charts 13).2.card.le
      have ht : Nat.card Q.top.range=32 := by rw [hH,BinaryMenuCayley8T22.exact_card]
      have hh := Q.kernelSpace_card_mul_top
      rw [ht] at hh
      omega
    · have hk : Nat.card Q.kernelSpace≤8 := by
        rw [hK,←BinaryHeisenbergEightNaturalHeads.kernel14_space,
          BinaryHeisenbergEightNaturalHeads.states_space]
        exact (BinaryHeisenbergEightNaturalHeads.charts 14).2.card.le
      have ht : Nat.card Q.top.range=32 := by rw [hH,BinaryMenuCayley8T22.exact_card]
      have hh := Q.kernelSpace_card_mul_top
      rw [ht] at hh
      omega

theorem sixteen_rank_six_head_three_derived_card_le_sixteen
    (hU : IsPGroup 2 U) (hrank : 6≤MarkedC4.genRank U)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hhead : 3≤Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    Nat.card (commutator U)≤16 := by
  have hu := E.sixteen_rank_six_head_three_source_card_le_1024 hU hrank W hhead
  have ha : 64≤Nat.card (Abelianization U) :=
    (show 2^6≤2^MarkedC4.genRank U from
      Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) hrank).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hU)
  have hh := (commutator U).card_mul_index
  change Nat.card (commutator U)*Nat.card (Abelianization U)=Nat.card U at hh
  nlinarith

theorem sixteen_rank_six_head_three_all_quotient_joint_le_256
    (hU : IsPGroup 2 U) (hrank : 6≤MarkedC4.genRank U)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hhead : 3≤Module.finrank (ZMod 2) W.toRepresentation.Coinvariants)
    (N : Subgroup U) [N.Normal] :
    Nat.card (commutator (U ⧸ N))*Nat.card (Subgroup.center (U ⧸ N))≤256 := by
  by_cases hc : ∀ a b : U ⧸ N,a*b=b*a
  · letI : IsMulCommutative (U ⧸ N) := ⟨⟨hc⟩⟩
    letI : CommGroup (U ⧸ N) := { (inferInstance : Group (U ⧸ N)) with mul_comm := hc }
    let f : Abelianization U →* U ⧸ N := Abelianization.lift (QuotientGroup.mk' N)
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N q
      exact ⟨Abelianization.of g,rfl⟩
    have hdegree : Nat.card X=16 := by simpa only [Nat.card_fin] using E.card_points
    have hAb := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
    rw [hdegree] at hAb
    norm_num at hAb
    have hQ : Nat.card (U ⧸ N)≤64 := (Nat.card_le_card_of_surjective f hf).trans hAb
    rw [commutator_eq_bot,Subgroup.card_bot,one_mul]
    exact (Nat.card_le_card_of_injective (Subgroup.center (U ⧸ N)).subtype
      Subtype.val_injective).trans (hQ.trans (by decide))
  · have hd := (SmallDerivedNormalFBounds.quotient_derived_card_le N).trans
      (E.sixteen_rank_six_head_three_derived_card_le_sixteen hU hrank W hhead)
    have hz := E.sixteen_rank_six_nonabelian_quotient_center_le_sixteen hU hrank N hc
    exact (Nat.mul_le_mul hd hz).trans (by norm_num)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
