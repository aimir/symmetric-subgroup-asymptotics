import SymmetricSubgroupAsymptotics.CFSGPrimeBinaryAbelianNormalOrder
import SymmetricSubgroupAsymptotics.CFSGPrimitiveBinaryFiveChiefBound
import SymmetricSubgroupAsymptotics.CFSGChiefPrimeFactorBudget

/-! Every faithful irreducible binary group in dimension five has abelian
chief charge at most four, for the chosen original series. The soluble
case has actual order dividing 930; the nonsoluble case uses its actual
self-centralizing simple normal subgroup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveBinaryFiveAllChiefBound

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] [Finite V]
  (rho : Representation (ZMod 2) G V)

theorem soluble_card_dvd_nineHundredThirty
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : Module.finrank (ZMod 2) V = 5) [IsSolvable G] : Nat.card G ∣ 930 := by
  by_cases hG : Subsingleton G
  · have hc : Nat.card G = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hG, ⟨1⟩⟩
    rw [hc]
    exact one_dvd _
  letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp hG
  obtain ⟨N, hN⟩ := PrimitiveSocleONanScottHelpers.exists_minimalNormal (G := G)
  letI : N.Normal := hN.1
  have hzero : ⁅N, N⁆ = ⊥ := by
    by_contra hh
    have he := hN.2.2 ⁅N, N⁆ inferInstance hh (Subgroup.commutator_le_self N)
    have hlt : ⁅N, N⁆ < N := IsSolvable.commutator_lt_of_ne_bot hN.2.1
    exact hlt.ne he
  letI : IsMulCommutative N := ⟨⟨fun x y => by
    apply Subtype.ext
    have hx := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero) x.property
    exact ((Subgroup.mem_centralizer_iff.mp hx) y y.property).symm⟩⟩
  exact CFSGPrimeBinaryAbelianNormalOrder.card_dvd_nineHundredThirty_of_abelian_normal
    rho hrho hf hd N hN.2.1

theorem chief_abelianLength_le_four
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : Module.finrank (ZMod 2) V = 5) (c : ActualChiefSeries G) :
    actualChiefSeriesAbelianLength c ≤ 4 := by
  by_cases hs : IsSolvable G
  · letI : IsSolvable G := hs
    have horder := soluble_card_dvd_nineHundredThirty rho hrho hf hd
    have hsmall := CFSGChiefPrimeFactorBudget.cardFactors_mono
      (by decide : 930 ≠ 0) horder
    have h930 : ArithmeticFunction.cardFactors 930 = 4 := by decide +kernel
    rw [h930] at hsmall
    exact (actualChiefSeriesAbelianLength_le_cardFactors c).trans hsmall
  · exact CFSGPrimitiveBinaryFiveChiefBound.chief_abelianLength_le_four
      hindex rho hrho hf hd hs c

end SymmetricSubgroupAsymptotics.CFSGPrimitiveBinaryFiveAllChiefBound
