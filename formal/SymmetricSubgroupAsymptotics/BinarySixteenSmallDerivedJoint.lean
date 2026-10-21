import SymmetricSubgroupAsymptotics.BinarySixteenRankSixIntegralNormals
import SymmetricSubgroupAsymptotics.BinaryPairSmallTopLargeKernel
import SymmetricSubgroupAsymptotics.OriginalKernelCenterProductBound
import SymmetricSubgroupAsymptotics.BinaryHeisenbergTopIntegralBounds
import SymmetricSubgroupAsymptotics.SmallDerivedNormalFBounds

/-! Small original derived order and the already checked sixteen-point
quotient-centre theorem combine before taking maxima. Every denominator
is literal. The original centre also retains its actual fixed-kernel factor.
No splitting is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance sixteenSmallDerivedJointPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]
include E

omit [MulAction.IsPretransitive U X] in
theorem original_center_card_le_two_mul_top_center
    [MulAction.IsPretransitive E.top.range (Fin 8)] :
    Nat.card (Subgroup.center U)≤2*Nat.card (Subgroup.center E.top.range) := by
  let M := E.kernelTopPermutationSubrepresentation
  have hdim := PermutationBinaryFourSection.subrepresentation_invariants_le_one (0 : Fin 8) M
  have hi : Nat.card M.toRepresentation.invariants≤2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M.toRepresentation.invariants)
    rw [Nat.card_zmod] at hh
    rw [hh]
    exact (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hdim).trans_eq (by decide)
  exact ((E.actualOriginalKernelChart).center_card_le_invariants_mul_center
    E.top.rangeRestrict_surjective).trans (Nat.mul_le_mul_right _ hi)

omit E [MulAction.IsPretransitive U X] in
theorem sixteen_rank_six_order_le_256_derived_card_le_four
    (hU : IsPGroup 2 U) (hrank : 6≤MarkedC4.genRank U)
    (hcard : Nat.card U≤256) : Nat.card (commutator U)≤4 := by
  have hAb : 64≤Nat.card (Abelianization U) := by
    exact (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hrank).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hU)
  have hh := (commutator U).card_mul_index
  change Nat.card (commutator U)*Nat.card (Abelianization U)=Nat.card U at hh
  nlinarith

theorem sixteen_rank_six_small_derived_all_quotient_joint_le_sixty_four
    (hU : IsPGroup 2 U) (hrank : 6≤MarkedC4.genRank U)
    (hD : Nat.card (commutator U)≤4)
    (N : Subgroup U) [N.Normal] :
    Nat.card (commutator (U ⧸ N))*Nat.card (Subgroup.center (U ⧸ N))≤64 := by
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
      Subtype.val_injective).trans hQ
  · have hd := (SmallDerivedNormalFBounds.quotient_derived_card_le N).trans hD
    have hz := E.sixteen_rank_six_nonabelian_quotient_center_le_sixteen hU hrank N hc
    exact (Nat.mul_le_mul hd hz).trans (by norm_num)

theorem sixteen_rank_six_small_order_heisenberg_top_joint_le_sixteen
    (hU : IsPGroup 2 U) (hrank : 6≤MarkedC4.genRank U)
    (hcard : Nat.card U≤256)
    (hH : E.top.range=BinaryHeisenbergEightNaturalHeads.H) :
    Nat.card (commutator U)*Nat.card (Subgroup.center U)≤16 := by
  letI : MulAction.IsPretransitive E.top.range (Fin 8) := E.top_pretransitive
  have hd := sixteen_rank_six_order_le_256_derived_card_le_four hU hrank hcard
  have ht : Nat.card (Subgroup.center E.top.range)≤2 :=
    (Nat.card_congr (Subgroup.centerCongr (MulEquiv.subgroupCongr hH)).toEquiv).le.trans
      BinaryHeisenbergTopIntegralBounds.center_card_le_two
  have hz := E.original_center_card_le_two_mul_top_center.trans
    (Nat.mul_le_mul_left 2 ht)
  exact (Nat.mul_le_mul hd hz).trans (by norm_num)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
