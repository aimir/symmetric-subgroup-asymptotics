import SymmetricSubgroupAsymptotics.CFSGSmallLinearSimpleOuterOrder
import SymmetricSubgroupAsymptotics.MarkedC4AbelianSectionSize

/-! A faithful simple action on at most64 original vectors has outer
automorphism order at most36 under sufficient simple-index bounds. Its
actual outer quotient spends at most five prime-factor units. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSmallLinearSimpleOuterSixtyFour
open PrimitiveSocleRawStructure

theorem outer_card_le_thirtySix
    {k S V : Type} [Field k] [Group S] [Finite S] [IsSimpleGroup S]
    [AddCommGroup V] [Module k V] [Finite V]
    (hindex : SufficientSimpleIndexBounds)
    (rho : Representation k S V) (hf : Function.Injective rho)
    (hnc : ¬ IsMulCommutative S) (hV : Nat.card V ≤ 64) : Nat.card (Outer S) ≤ 36 := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex S
  have he := (CFSGSmallLinearSimpleOuterOrder.leastProperIndex_le_module_card rho hf ell hell).trans hV
  obtain ⟨_,hb⟩ := hindex S hnc ell hell
  have hp : 0 < ell := by
    have hh := nonabelianSimple_leastProperIndex_five_le
      (fun h => hnc (isMulCommutative_iff.mpr h)) hell.1
    omega
  have hout := hb.log_six_of_le hp he
  have hl : Real.logb 2 (64:ℝ)=6 := by
    rw [show (64:ℝ)=2^6 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
    norm_num
  norm_num only [Nat.cast_ofNat] at hout
  rw [hl] at hout
  norm_num at hout
  exact_mod_cast hout

theorem cardFactors_le_five_of_le_thirtySix {n : ℕ} (hn : n ≠ 0) (hs : n ≤ 36) :
    ArithmeticFunction.cardFactors n ≤ 5 := by
  have hp : 2^(ArithmeticFunction.cardFactors n) ≤ n := by
    simpa only [ArithmeticFunction.cardFactors_apply,MarkedC4.AbelianSectionSize.omega] using
      MarkedC4.AbelianSectionSize.two_pow_omega_le hn
  have hh : 2^(ArithmeticFunction.cardFactors n)<2^6 := hp.trans_lt (by omega)
  have hlt := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp hh
  omega

end SymmetricSubgroupAsymptotics.CFSGSmallLinearSimpleOuterSixtyFour
