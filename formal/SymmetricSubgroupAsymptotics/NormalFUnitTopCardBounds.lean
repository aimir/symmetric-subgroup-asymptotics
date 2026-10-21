import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds

/-! A unit-coefficient normal-F packet from bounds on the same actual
quotient.  The centralizer of the whole quotient is its literal centre. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem normalF_unit_top_packet_of_card_bounds
    {Q : Type} [Group Q] [Finite Q] (d z : ℕ)
    (hd : Nat.card (commutator Q) ≤ 2 ^ d)
    (hz : Nat.card (Subgroup.center Q) ≤ 2 ^ z)
    (hcost : d + z ≤ 8) (hzcost : z ≤ 4) :
    ∃ W : Subgroup Q, W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  have hlog (n k : ℕ) (hn : 0 < n) (hk : n ≤ 2 ^ k) :
      Real.logb 2 (n : ℝ) ≤ k := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hn)).mpr
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using
      (show (n : ℝ) ≤ (2 ^ k : ℕ) by exact_mod_cast hk)
  have hdlog : MarkedC4.ActualNormalFMarkedPeel.commutatorLog
      (⊤ : Subgroup Q) ≤ d := hlog _ d Nat.card_pos hd
  have hzlog : MarkedC4.ActualNormalFMarkedPeel.centralLog
      (⊤ : Subgroup Q) ≤ z := by
    simpa only [MarkedC4.ActualNormalFMarkedPeel.centralLog,
      MarkedC4.RDTNormalFInterface.targetCentralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ] using hlog _ z Nat.card_pos hz
  have hbudget : (d : ℝ) + z ≤ 8 := by exact_mod_cast hcost
  have hzbudget : (z : ℝ) ≤ 4 := by exact_mod_cast hzcost
  exact ⟨⊤, inferInstance, by linarith, hzlog.trans hzbudget⟩

end SymmetricSubgroupAsymptotics
