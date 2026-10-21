import SymmetricSubgroupAsymptotics.NormalFPacketOfActualCards

/-! Joint integral order budgets for the SAME actual normal F convert
directly into the exact RDT normal-F logarithmic budgets. Separate rounded
powers for the two factors are unnecessary. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface

private theorem normalF_logb_card_le (n k : ℕ) (hn : 0<n) (hk : n≤2^k) :
    Real.logb 2 (n : ℝ)≤k := by
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2)
    (by exact_mod_cast hn)).mpr
  simpa only [Real.rpow_natCast,Nat.cast_pow,Nat.cast_ofNat] using
    (show (n : ℝ)≤(2^k : ℕ) by exact_mod_cast hk)

/-- The product retains cancellation between the two actual order costs. -/
theorem normalF_unit_packet_of_actual_product_bound
    {Q : Type} [Group Q] [Finite Q] (F : Subgroup Q) [F.Normal]
    (b c : ℕ)
    (hproduct : Nat.card (targetCommutator F)*Nat.card (targetCentralizer F)≤2^b)
    (hcenter : Nat.card (targetCentralizer F)≤2^c) :
    commutatorLog F+centralLog F≤b ∧ centralLog F≤c := by
  have hd : (0 : ℝ)<Nat.card (targetCommutator F) := by exact_mod_cast Nat.card_pos
  have hz : (0 : ℝ)<Nat.card (targetCentralizer F) := by exact_mod_cast Nat.card_pos
  have he : commutatorLog F+centralLog F=
      Real.logb 2 ((Nat.card (targetCommutator F)*Nat.card (targetCentralizer F) : ℕ) : ℝ) := by
    rw [Nat.cast_mul,Real.logb_mul hd.ne' hz.ne']
    rfl
  refine ⟨?_,normalF_logb_card_le _ c Nat.card_pos hcenter⟩
  rw [he]
  exact normalF_logb_card_le _ b (Nat.mul_pos Nat.card_pos Nat.card_pos) hproduct

/-- The exact five-quarters budget is an integer fourth-power product
inequality, still referring to one SAME ambient normal subgroup. -/
theorem normalF_fiveQuarter_packet_of_actual_product_bound
    {Q : Type} [Group Q] [Finite Q] (F : Subgroup Q) [F.Normal]
    (b c : ℕ)
    (hproduct : Nat.card (targetCommutator F)^4*Nat.card (targetCentralizer F)^5≤2^(4*b))
    (hcenter : Nat.card (targetCentralizer F)≤2^c) :
    commutatorLog F+(5/4 : ℝ)*centralLog F≤b ∧ centralLog F≤c := by
  have hd : (0 : ℝ)<Nat.card (targetCommutator F) := by exact_mod_cast Nat.card_pos
  have hz : (0 : ℝ)<Nat.card (targetCentralizer F) := by exact_mod_cast Nat.card_pos
  have he :
      Real.logb 2 ((Nat.card (targetCommutator F)^4*Nat.card (targetCentralizer F)^5 : ℕ) : ℝ)=
        4*commutatorLog F+5*centralLog F := by
    rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,
      Real.logb_mul (pow_ne_zero _ hd.ne') (pow_ne_zero _ hz.ne'),
      Real.logb_pow,Real.logb_pow]
    rfl
  have hb := normalF_logb_card_le _ (4*b)
    (Nat.mul_pos (Nat.pow_pos Nat.card_pos) (Nat.pow_pos Nat.card_pos)) hproduct
  rw [he,Nat.cast_mul,Nat.cast_ofNat] at hb
  exact ⟨by linarith,normalF_logb_card_le _ c Nat.card_pos hcenter⟩

end SymmetricSubgroupAsymptotics
