import SymmetricSubgroupAsymptotics.BinaryRankAdditiveNormalFTopCriterion

/-! The actual rank-additive joint formula can use an independently
proved centre bound on the SAME quotient. This avoids adding separate
worst-case exponents for the kernel and the retained top centre. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance rankAdditiveJointOnlyFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem binary_rank_additive_normalF_top_unit_criterion_of_quotient_center
    {G B Q H : Type} [Group G] [Finite G] [Group B] [Finite B]
    [Group Q] [Finite Q] [Group H] [Finite H]
    (hG : IsPGroup 2 G) (beta : G →* B) (hbeta : Function.Surjective beta)
    (hpow : ∀ k : beta.ker,(k : G)^2=1)
    (hexp : ∀ a : Abelianization G,a^2=1)
    (hrank : MarkedC4.genRank G=MarkedC4.normalGen beta.ker+MarkedC4.genRank B)
    (q : G →* Q) (hq : Function.Surjective q) (hqker : q.ker≤commutator G)
    (d w t b c : ℕ)
    (hbound : ∀ (A : Subgroup G) [A.Normal],A≤beta.ker → MarkedC4.normalGen A≤d)
    (f : Q →* H) (hf : Function.Surjective f) (hfker : f.ker=beta.ker.map q)
    (hW : Nat.card (beta.ker.map q)≤2^w)
    (hjointH : Nat.card (commutator H)*Nat.card (Subgroup.center H)≤2^t)
    (hcost : d+w+t≤MarkedC4.normalGen beta.ker+b)
    (hcenter : Nat.card (Subgroup.center Q)≤2^c) :
    ∃ F : Subgroup Q,F.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog F+
        MarkedC4.ActualNormalFMarkedPeel.centralLog F≤b ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog F≤c := by
  have hmain := pGroup_quotient_derived_center_joint_bound_of_rank_additivity
    2 hG beta hbeta hpow hexp hrank q hq hqker d hbound f hf hfker
  have hright : 2^d*Nat.card (beta.ker.map q)*Nat.card (commutator H)*
      Nat.card (Subgroup.center H)≤2^(MarkedC4.normalGen beta.ker+b) := by
    calc
      _ = (2^d*Nat.card (beta.ker.map q))*
          (Nat.card (commutator H)*Nat.card (Subgroup.center H)) := by ring
      _ ≤ (2^d*2^w)*2^t := Nat.mul_le_mul (Nat.mul_le_mul_left _ hW) hjointH
      _ = 2^(d+w+t) := by rw [pow_add,pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0<2) hcost
  have hproduct : Nat.card (commutator Q)*Nat.card (Subgroup.center Q)≤2^b := by
    have hh := hmain.trans hright
    rw [pow_add] at hh
    exact Nat.le_of_mul_le_mul_left hh (Nat.pow_pos (by decide : 0<2))
  have hp := normalF_unit_packet_of_actual_product_bound (⊤ : Subgroup Q) b c (by
    simpa only [MarkedC4.RDTNormalFInterface.targetCommutator,
      MarkedC4.RDTNormalFInterface.targetCentralizer,Subgroup.coe_top,
      Subgroup.centralizer_univ] using hproduct) (by
    simpa only [MarkedC4.RDTNormalFInterface.targetCentralizer,Subgroup.coe_top,
      Subgroup.centralizer_univ] using hcenter)
  exact ⟨⊤,inferInstance,hp.1,hp.2⟩
end SymmetricSubgroupAsymptotics
