import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds
import Mathlib.GroupTheory.PGroup

/-! One bit of extra original derived capacity is absorbed when passing
from the5/4 coefficient to coefficient1. The positive central bit is
proved from the SAME actual nonabelian binary quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

theorem unit_packet_of_doubled_joint_card_bounds
    {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (hnonab : ¬ ∀ a b : Q, a * b = b * a)
    (d z : ℕ) (hd : Nat.card (commutator Q) ≤ 2 ^ (d + 1))
    (hz : Nat.card (Subgroup.center Q) ≤ 2 ^ z)
    (hcost : 4 * d + 5 * z ≤ 32) (hzcost : z ≤ 4) :
    ∃ V : Subgroup Q, V.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog V +
        MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 4 := by
  letI : Nontrivial Q := not_subsingleton_iff_nontrivial.mp
    (fun h => hnonab (fun a b => @Subsingleton.elim Q h (a * b) (b * a)))
  letI : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  have hc : 1 < Nat.card (Subgroup.center Q) := Finite.one_lt_card
  have hzp : 0 < z := by
    by_contra h
    have he : z = 0 := by omega
    rw [he, pow_zero] at hz
    omega
  have hbudget : d + 1 + z ≤ 8 := by omega
  have hlog (n k : ℕ) (hn : 0 < n) (hk : n ≤ 2 ^ k) :
      Real.logb 2 (n : ℝ) ≤ k := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hn)).mpr
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using
      (show (n : ℝ) ≤ (2 ^ k : ℕ) by exact_mod_cast hk)
  have hdlog : MarkedC4.ActualNormalFMarkedPeel.commutatorLog (⊤ : Subgroup Q) ≤ d + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlog _ (d + 1) Nat.card_pos hd
  have hzlog : MarkedC4.ActualNormalFMarkedPeel.centralLog (⊤ : Subgroup Q) ≤ z := by
    simpa only [MarkedC4.ActualNormalFMarkedPeel.centralLog,
      MarkedC4.RDTNormalFInterface.targetCentralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ] using hlog _ z Nat.card_pos hz
  have hb : (d : ℝ) + 1 + z ≤ 8 := by exact_mod_cast hbudget
  have hzb : (z : ℝ) ≤ 4 := by exact_mod_cast hzcost
  exact ⟨⊤, inferInstance, by linarith, hzlog.trans hzb⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
