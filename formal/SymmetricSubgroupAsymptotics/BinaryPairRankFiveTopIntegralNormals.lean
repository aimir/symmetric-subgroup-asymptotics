import SymmetricSubgroupAsymptotics.BinarySixteenExcessOneIntegralNormals
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenRankFiveExcessOne
import SymmetricSubgroupAsymptotics.BinaryPairKernelNormalGenerators
import SymmetricSubgroupAsymptotics.BinaryPairLiftCarryExponent
import SymmetricSubgroupAsymptotics.ElementaryBinaryTransitiveNormalRank

/-! Full integral proper-normal orders across an original sixteen-pair
frame with rank-five actual top. The smaller-top theorem is applied to
that top's actual sixteen-point permutation action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))

theorem rank_five_top_proper_normal_integral_order_le_256
    (hU : IsPGroup 2 U) (hTopRank : MarkedC4.genRank F.top.range = 5)
    (hAb : Nat.card (Abelianization U) ≤ 512)
    (E : Subgroup U) [E.Normal] (hproper : E ≠ ⊤) :
    normalIntegralCoinvariantOrder E ≤ 256 := by
  letI rankFiveTopIntegral_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI rankFiveTopIntegral_topTransitive : MulAction.IsPretransitive F.top.range (Fin 16) :=
    F.top_pretransitive
  letI rankFiveTopIntegral_pairAction : MulAction U (Fin 16) := MulAction.compHom (Fin 16) F.top
  letI rankFiveTopIntegral_pairTransitive : MulAction.IsPretransitive U (Fin 16) := ⟨by
    intro i j
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i j
    obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
    exact ⟨u, ht⟩⟩
  have hact : ∀ (u : U) (i : Fin 16), u • i = F.top u i := fun _ _ => rfl
  have hTop := F.top_isPGroup hU
  letI rankFiveTopIntegral_topNilpotent : Group.IsNilpotent F.top.range := hTop.isNilpotent
  have hTopTrans : ∀ x y : Fin 16, ∃ t : F.top.range, t.val x = y :=
    fun x y => MulAction.exists_smul_eq F.top.range x y
  have hTopExcess := binary_degree_sixteen_hasExcess_one_of_genRank_five
    F.top.range hTop hTopTrans hTopRank
  have hnon : ¬ BinarySquareActionStructure.SquaresActTrivially (G := U) (X := Fin 16) := by
    intro hel
    have hTopEl : BinarySquareActionStructure.SquaresActTrivially
        (G := F.top.range) (X := Fin 16) := by
      intro t i
      obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
      rw [← map_pow]
      exact (hact (u ^ 2) i).symm.trans (hel u i)
    have hb := ElementaryBinaryTransitiveNormalRank.normalGen_le_exponent hTopEl
      (0 : Fin 16) 4 (Nat.card_fin 16) (⊤ : Subgroup F.top.range)
    have hg := MarkedC4.genRank_le_normalGen_top (G := F.top.range)
    omega
  let f := F.top.rangeRestrict
  have hf : Function.Surjective f := F.top.rangeRestrict_surjective
  by_cases hfull : E.map f = ⊤
  · letI rankFiveTopIntegral_kernelComm : IsMulCommutative F.top.ker := ⟨⟨fun a b =>
      F.bitsHom_injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
    have hsup : E ⊔ F.top.ker = ⊤ := by
      have h := congrArg (Subgroup.comap f) hfull
      simpa only [Subgroup.comap_map_eq, Subgroup.comap_top, f,
        MonoidHom.ker_rangeRestrict] using h
    have he := relative_integral_order_mul_index_of_abelian_supplement E F.top.ker hsup
    have hi : 2 ≤ E.index := E.one_lt_index_of_ne_top hproper
    have hm : (⁅E, (⊤ : Subgroup U)⁆).relIndex E * 2 ≤ 512 :=
      (Nat.mul_le_mul_left _ hi).trans (he.le.trans hAb)
    exact Nat.le_of_mul_le_mul_right hm (by decide : 0 < (2 : ℕ))
  letI rankFiveTopIntegral_imageNormal : (E.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hTint : normalIntegralCoinvariantOrder (E.map f) ≤ 16 :=
    binary_sixteen_excess_one_proper_normal_integral_order_le_sixteen
      F.top.range hTop hTopTrans hTopExcess (E.map f) hfull
  have hpowers : ∀ k : f.ker, (k : U) ^ 2 = 1 := by
    intro k
    exact F.physical_kernel_pow_two
      ⟨k.val, by simpa only [f, MonoidHom.ker_rangeRestrict] using k.property⟩
  have hb := normalIntegralCoinvariantOrder_le_elementary_kernel 2 hU f hf hpowers E
  dsimp only [f] at hb
  rw [MonoidHom.ker_rangeRestrict] at hb
  have hhead : MarkedC4.normalGen (E ⊓ F.top.ker) ≤ 4 := by
    simpa only [Nat.card_fin] using F.normalGen_le_quarter_of_not_elementary
      hact hU hnon (E ⊓ F.top.ker) (show E ⊓ F.top.ker ≤ F.top.ker from inf_le_right)
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hhead
  exact hb.trans (Nat.mul_le_mul hp hTint)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
