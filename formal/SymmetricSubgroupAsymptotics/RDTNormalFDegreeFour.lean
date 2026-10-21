import SymmetricSubgroupAsymptotics.SmallBinaryNormalFBounds
import Mathlib.GroupTheory.Perm.Finite

/-! The degree-four normal-F packet follows from original binary order
alone. No finite action catalogue or rank-preserving quotient premise is
needed at this endpoint. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RDTNormalFDegreeFour
open MarkedC4 MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface

variable {Q : Type} [Group Q] [Finite Q]

theorem two_le_genRank_of_nonabelian (hnonab : ¬∀ a b : Q,a*b=b*a) :
    2≤genRank Q := by
  by_contra hnot
  obtain ⟨S,hS,hgen⟩ := genRank_spec (G := Q)
  have hsmall : S.card≤1 := by omega
  have hcomm := Subgroup.isMulCommutative_closure (k := (S : Set Q)) (by
    intro x hx y hy
    have he : x=y := Finset.card_le_one.mp hsmall x hx y hy
    rw [he])
  rw [hgen] at hcomm
  apply hnonab
  intro a b
  exact congrArg Subtype.val (hcomm.is_comm.comm
    (⟨a,Subgroup.mem_top a⟩ : (⊤ : Subgroup Q))
    (⟨b,Subgroup.mem_top b⟩ : (⊤ : Subgroup Q)))

theorem top_log_bounds_of_card_le_eight (hQ : IsPGroup 2 Q)
    (hcard : Nat.card Q≤8) (hnonab : ¬∀ a b : Q,a*b=b*a) :
    commutatorLog (⊤ : Subgroup Q)+centralLog (⊤ : Subgroup Q)≤2 ∧
      centralLog (⊤ : Subgroup Q)≤1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : 4≤2^genRank Q := Nat.pow_le_pow_right (by decide : 0<(2 : ℕ))
    (two_le_genRank_of_nonabelian hnonab)
  have hab := pGroup_pow_genRank_le_abelianization_card 2 hQ
  have hf := (commutator Q).card_eq_card_quotient_mul_card_subgroup
  change Nat.card Q=Nat.card (Abelianization Q)*Nat.card (commutator Q) at hf
  have hd : Nat.card (commutator Q)≤2 := by nlinarith
  have hz : Nat.card (Subgroup.center Q)≤2 := by
    have hi := SmallBinaryNormalFBounds.nonabelian_center_index_four_le hnonab
    have hf := (Subgroup.center Q).card_mul_index
    nlinarith
  have hlog (n : ℕ) (hn : 0<n) (htwo : n≤2) : Real.logb 2 (n : ℝ)≤1 := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2)
      (by exact_mod_cast hn)).mpr
    norm_num
    exact_mod_cast htwo
  have hdl : commutatorLog (⊤ : Subgroup Q)≤1 :=
    hlog _ (Nat.card_pos (α := commutator Q)) hd
  have hzl : centralLog (⊤ : Subgroup Q)≤1 := by
    simpa only [centralLog,targetCentralizer,Subgroup.coe_top,Subgroup.centralizer_univ]
      using hlog _ (Nat.card_pos (α := Subgroup.center Q)) hz
  exact ⟨by linarith,hzl⟩

theorem original_card_le_eight (G : Subgroup (Equiv.Perm (Fin 4)))
    (hG : IsPGroup 2 G) : Nat.card G≤8 := by
  have hp : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hd : Nat.card G∣24 := by
    simpa only [hp] using G.card_subgroup_dvd_card
  obtain ⟨k,hk⟩ := hG.exists_card_eq
  have hkle : k≤3 := by
    by_contra hh
    have h16 : 2^4∣Nat.card G := by
      rw [hk]
      exact pow_dvd_pow 2 (by omega : 4≤k)
    have hbad : 16∣24 := h16.trans hd
    norm_num at hbad
  rw [hk]
  exact Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) hkle

theorem quotient_packet (G : Subgroup (Equiv.Perm (Fin 4)))
    (hG : IsPGroup 2 G) (N : Subgroup G) [N.Normal]
    (hnonab : ¬∀ a b : G ⧸ N,a*b=b*a) :
    ∃ F : Subgroup (G ⧸ N),F.Normal ∧
      commutatorLog F+centralLog F≤2 ∧ centralLog F≤1 := by
  have hq : Nat.card (G ⧸ N)≤8 :=
    (Nat.le_of_dvd (Nat.card_pos (α := G)) N.index_dvd_card).trans (original_card_le_eight G hG)
  have hb := top_log_bounds_of_card_le_eight (hG.to_quotient N) hq hnonab
  exact ⟨⊤,inferInstance,hb.1,hb.2⟩

end SymmetricSubgroupAsymptotics.RDTNormalFDegreeFour
