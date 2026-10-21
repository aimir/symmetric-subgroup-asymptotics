import SymmetricSubgroupAsymptotics.SmallBinaryNormalIntegralCoinvariants
import SymmetricSubgroupAsymptotics.NormalIntegralCoinvariantExtension
import SymmetricSubgroupAsymptotics.BinaryPairSmallTopSectionOrders
import SymmetricSubgroupAsymptotics.BinaryPairKernelNormalGenerators
import SymmetricSubgroupAsymptotics.BinaryPairLiftCarryExponent

/-! Integral relative orders for EVERY actual proper normal of a residual
nonelementary eight-pair source with top order at most32. Actual full-top
image uses its elementary kernel as abelian supplement. Proper top image
uses the integral extension theorem, retaining higher cyclic factors. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction U (Fin 8)]
    [MulAction.IsPretransitive U (Fin 8)]
    (hact : ∀ (u : U) (i : Fin 8), u • i = F.top u i)

include hact in
/-- This bounds the INTEGRAL quotient E/[E,U], not only its binary head. -/
theorem small_pair_top_proper_normal_integral_order_le_sixteen
    (hU : IsPGroup 2 U)
    (hnon : ¬ BinarySquareActionStructure.SquaresActTrivially (G := U) (X := Fin 8))
    (htop : Nat.card F.top.range ≤ 32)
    (htoprank : MarkedC4.genRank F.top.range ≤ 3)
    (hrank : MarkedC4.genRank U = 5)
    (hexp : ∀ a : Abelianization U, a ^ 2 = 1)
    (E : Subgroup U) [E.Normal] (hproper : E ≠ ⊤) :
    normalIntegralCoinvariantOrder E ≤ 16 := by
  letI smallPairTopIntegral_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := F.top.rangeRestrict
  have hf : Function.Surjective f := F.top.rangeRestrict_surjective
  have hTop := F.top_isPGroup hU
  have hTopExp := abelianization_exponent_of_surjective f hf 2 hexp
  have hTopAb : Nat.card (Abelianization F.top.range) ≤ 8 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hTop hTopExp]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) htoprank
  have hAb : Nat.card (Abelianization U) = 32 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hU hexp, hrank]
    decide
  by_cases hfull : E.map f = ⊤
  · letI smallPairTopIntegral_kernelComm : IsMulCommutative F.top.ker := ⟨⟨fun a b =>
      F.bitsHom_injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
    have hsup : E ⊔ F.top.ker = ⊤ := by
      have h := congrArg (Subgroup.comap f) hfull
      simpa only [Subgroup.comap_map_eq, Subgroup.comap_top, f,
        MonoidHom.ker_rangeRestrict] using h
    have he := relative_integral_order_mul_index_of_abelian_supplement E F.top.ker hsup
    rw [hAb] at he
    have hi : 2 ≤ E.index := E.one_lt_index_of_ne_top hproper
    change (⁅E, (⊤ : Subgroup U)⁆).relIndex E ≤ 16
    have hm : (⁅E, (⊤ : Subgroup U)⁆).relIndex E * 2 ≤ 32 :=
      (Nat.mul_le_mul_left _ hi).trans he.le
    omega
  · letI smallPairTopIntegral_imageNormal : (E.map f).Normal :=
      Subgroup.Normal.map inferInstance f hf
    have hsmall := small_binary_proper_normal_integral_order_le_four hTop htop hTopAb
      (E.map f) hfull
    change normalIntegralCoinvariantOrder (E.map f) ≤ 4 at hsmall
    have hpowers : ∀ k : f.ker, (k : U) ^ 2 = 1 := by
      intro k
      exact F.physical_kernel_pow_two ⟨k.val, by
        simpa only [f, MonoidHom.ker_rangeRestrict] using k.property⟩
    have hbound := normalIntegralCoinvariantOrder_le_elementary_kernel 2 hU f hf hpowers E
    have hhead : MarkedC4.normalGen (E ⊓ f.ker) ≤ 2 := by
      have hh := F.normalGen_le_quarter_of_not_elementary hact hU hnon
        (E ⊓ F.top.ker) inf_le_right
      simpa only [f, MonoidHom.ker_rangeRestrict, Nat.card_fin] using hh
    exact hbound.trans (by
      have hm := Nat.mul_le_mul
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hhead) hsmall
      exact hm)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
