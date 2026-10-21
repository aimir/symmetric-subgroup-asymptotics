import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalFMarkedPeel

/-! A smaller coefficient costs less on the SAME actual centralizer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface

theorem centralLog_nonneg {G : Type} [Group G] [Finite G] (F : Subgroup G) :
    0 ≤ centralLog F := by
  apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
  exact_mod_cast (Nat.succ_le_of_lt (Nat.card_pos (α := targetCentralizer F)))

theorem normalF_packet_coefficient_mono
    {G : Type} [Group G] [Finite G] (a c b z : ℝ) (hac : a ≤ c)
    (h : ∃ F : Subgroup G, F.Normal ∧ commutatorLog F + c*centralLog F ≤ b ∧ centralLog F ≤ z) :
    ∃ F : Subgroup G, F.Normal ∧ commutatorLog F + a*centralLog F ≤ b ∧ centralLog F ≤ z := by
  obtain ⟨F,hF,hcost,hz⟩ := h
  exact ⟨F,hF,(add_le_add le_rfl (mul_le_mul_of_nonneg_right hac (centralLog_nonneg F))).trans hcost,hz⟩

end SymmetricSubgroupAsymptotics
