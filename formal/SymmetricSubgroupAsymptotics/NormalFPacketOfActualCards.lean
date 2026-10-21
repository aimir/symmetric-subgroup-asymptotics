import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalFMarkedPeel

/-! The two bounds concern one SAME actual normal subgroup. It can be
proper; neither factor is replaced by the centre or derived group of the
whole quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface

theorem normalF_unit_packet_of_actual_card_bounds
    {Q : Type} [Group Q] [Finite Q] (F : Subgroup Q) [F.Normal]
    (d z b c : ℕ)
    (hd : Nat.card (targetCommutator F) ≤ 2 ^ d)
    (hz : Nat.card (targetCentralizer F) ≤ 2 ^ z)
    (hcost : d + z ≤ b) (hcenter : z ≤ c) :
    commutatorLog F + centralLog F ≤ b ∧ centralLog F ≤ c := by
  have hlog (n k : ℕ) (hn : 0 < n) (hk : n ≤ 2 ^ k) :
      Real.logb 2 (n : ℝ) ≤ k := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hn)).mpr
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using
      (show (n : ℝ) ≤ (2 ^ k : ℕ) by exact_mod_cast hk)
  have hdl : commutatorLog F ≤ d := hlog _ d Nat.card_pos hd
  have hzl : centralLog F ≤ z := hlog _ z Nat.card_pos hz
  have hb : (d : ℝ) + z ≤ b := by exact_mod_cast hcost
  have hc : (z : ℝ) ≤ c := by exact_mod_cast hcenter
  exact ⟨by linarith, hzl.trans hc⟩

end SymmetricSubgroupAsymptotics
