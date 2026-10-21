import SymmetricSubgroupAsymptotics.BinarySixtyFourIntegralNormals
import SymmetricSubgroupAsymptotics.BinaryPairSmallTopIntegralNormals

/-! Every proper original normal of a nonelementary eight-pair source
with top order at most sixty-four satisfies the integral bound. The center
bound comes from that actual faithful top action, without finite models. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction U (Fin 8)]
    [MulAction.IsPretransitive U (Fin 8)]
    (hact : ∀ (u : U) (i : Fin 8), u • i = F.top u i)

include hact in
theorem sixtyfour_pair_top_proper_normal_integral_order_le_sixteen
    (hU : IsPGroup 2 U)
    (hnon : ¬ BinarySquareActionStructure.SquaresActTrivially (G := U) (X := Fin 8))
    (htop : Nat.card F.top.range ≤ 64)
    (hAb : Nat.card (Abelianization U) ≤ 32)
    (hTopAb : Nat.card (Abelianization F.top.range) ≤ 8)
    (E : Subgroup U) [E.Normal] (hproper : E ≠ ⊤) :
    normalIntegralCoinvariantOrder E ≤ 16 := by
  letI sixtyfourPairIntegral_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := F.top.rangeRestrict
  have hf : Function.Surjective f := F.top.rangeRestrict_surjective
  have hTop := F.top_isPGroup hU
  letI sixtyfourPairIntegral_topTransitive : MulAction.IsPretransitive F.top.range (Fin 8) := ⟨by
    intro i j
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U i j
    exact ⟨f u, (hact u i).symm.trans hu⟩⟩
  by_cases hfull : E.map f = ⊤
  · letI sixtyfourPairIntegral_kernelComm : IsMulCommutative F.top.ker := ⟨⟨fun a b =>
      F.bitsHom_injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
    have hsup : E ⊔ F.top.ker = ⊤ := by
      have h := congrArg (Subgroup.comap f) hfull
      simpa only [Subgroup.comap_map_eq, Subgroup.comap_top, f,
        MonoidHom.ker_rangeRestrict] using h
    have he := relative_integral_order_mul_index_of_abelian_supplement E F.top.ker hsup
    have hi : 2 ≤ E.index := E.one_lt_index_of_ne_top hproper
    change (⁅E, (⊤ : Subgroup U)⁆).relIndex E ≤ 16
    nlinarith
  letI sixtyfourPairIntegral_imageNormal : (E.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hTint : normalIntegralCoinvariantOrder (E.map f) ≤ 4 := by
    by_cases hsmall : Nat.card F.top.range ≤ 32
    · exact small_binary_proper_normal_integral_order_le_four hTop hsmall hTopAb (E.map f) hfull
    · have hz := transitive_binary_degree_eight_center_card_le_four F.top.range hTop
        (show 8 < Nat.card F.top.range by omega)
      exact binary_proper_normal_integral_order_le_four_of_card_le_sixtyfour
        hTop htop hTopAb hz (E.map f) hfull
  have hpowers : ∀ k : f.ker, (k : U) ^ 2 = 1 := by
    intro k
    exact F.physical_kernel_pow_two ⟨k.val, by simpa only [f, MonoidHom.ker_rangeRestrict] using k.property⟩
  have hb := normalIntegralCoinvariantOrder_le_elementary_kernel 2 hU f hf hpowers E
  dsimp only [f] at hb
  rw [MonoidHom.ker_rangeRestrict] at hb
  have hhead : MarkedC4.normalGen (E ⊓ F.top.ker) ≤ 2 := by
    simpa only [Nat.card_fin] using F.normalGen_le_quarter_of_not_elementary
      hact hU hnon (E ⊓ F.top.ker) (show E ⊓ F.top.ker ≤ F.top.ker from inf_le_right)
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hhead
  exact hb.trans (Nat.mul_le_mul hp hTint)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
