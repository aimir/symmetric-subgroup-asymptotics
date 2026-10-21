import SymmetricSubgroupAsymptotics.CFSGAlternatingStarGenerators
import Mathlib.Tactic.NormNum

/-! Local geometry of actual 3-cycles. The proofs use three-point
supports and actual permutation equations, rather than a group census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleGeometry
open Equiv Equiv.Perm CFSGAlternatingStarGenerators
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A three-point support has exactly the two possible orientations. -/
theorem eq_or_eq_inv_of_support_eq (p q : Perm α) (hp : p.IsThreeCycle)
    (hq : q.IsThreeCycle) (hs : p.support=q.support) : q=p ∨ q=p⁻¹ := by
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by rw [hp.card_support];omega)
  have hxq : x∈q.support := hs ▸ hx
  have hps := hp.support_eq_iff_mem_support.mpr hx
  have hqs := hq.support_eq_iff_mem_support.mpr hxq
  have hpn := hp.nodup_iff_mem_support.mpr hx
  have hqn := hq.nodup_iff_mem_support.mpr hxq
  have hqx : q x∈p.support := hs.symm ▸ (apply_mem_support.mpr hxq)
  have hqxx : q (q x)∈p.support := hs.symm ▸ (apply_mem_support.mpr (apply_mem_support.mpr hxq))
  rw [hps] at hqx hqxx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hqx hqxx
  have heq := hq.eq_swap_mul_swap_iff_mem_support.mpr hxq
  have hep := hp.eq_swap_mul_swap_iff_mem_support.mpr hx
  change q=cycle x (q x) (q (q x)) at heq
  change p=cycle x (p x) (p (p x)) at hep
  rcases (show q x=p x ∨ q x=p (p x) by grind) with h | h
  · left
    have hh : q (q x)=p (p x) := by grind
    rw [heq,hep,hh,h]
  · right
    have hh : q (q x)=p x := by grind
    rw [heq,hep,hh,h,cycle_inverse]
    exact cycle_rotate x (p (p x)) (p x) (by grind) (by grind) (by grind)

/-- Nonidentity involutory products of two 3-cycles identify an oriented
common edge and two distinct remaining points. -/
theorem pair_normal_form (p q : Perm α) (hp : p.IsThreeCycle)
    (hq : q.IsThreeCycle) (hpq : (p*q)^2=1) (hne : p*q≠1) :
    ∃ a b c d : α, [a,b,c,d].Nodup ∧ p=cycle a b c ∧ q=cycle a b d := by
  have hsub : ¬q.support⊆p.support := by
    intro hs
    have he : p.support=q.support := (Finset.eq_of_subset_of_card_le hs
      (by rw [hp.card_support,hq.card_support])).symm
    rcases eq_or_eq_inv_of_support_eq p q hp hq he with h | h
    · subst q
      have hfour : p^4=1 := by simpa only [pow_succ,pow_zero,mul_one,mul_assoc] using hpq
      have hd := orderOf_dvd_of_pow_eq_one hfour
      rw [hp.orderOf] at hd
      norm_num at hd
    · exact hne (by rw [h,mul_inv_cancel])
  obtain ⟨d,hdq,hdp⟩ : ∃ d,d∈q.support ∧ d∉p.support := by
    by_contra h
    apply hsub
    intro d hd
    by_contra hn
    exact h ⟨d,hd,hn⟩
  have hpd : p d=d := by simpa only [notMem_support] using hdp
  have hqn := hq.nodup_iff_mem_support.mpr hdq
  have hqc : q (q (q d))=d := by
    have h := congrArg (fun r : Perm α => r d) (pow_orderOf_eq_one q)
    simpa only [hq.orderOf,pow_succ,pow_zero,Perm.mul_apply,Perm.one_apply] using h
  have he := congrArg (fun r : Perm α => r d) hpq
  change p (q (p (q d)))=d at he
  have hab : p (q d)=q (q d) := by
    apply q.injective
    apply p.injective
    rw [he,hqc,hpd]
  have ha : q d∈p.support := by rw [mem_support,hab];grind
  have hpn := hp.nodup_iff_mem_support.mpr ha
  refine ⟨q d,q (q d),p (q (q d)),d,?_,?_,?_⟩
  · have hs := hp.support_eq_iff_mem_support.mpr ha
    rw [hab] at hpn hs
    rw [hs] at hdp
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hdp
    grind
  · have h := hp.eq_swap_mul_swap_iff_mem_support.mpr ha
    change p=cycle (q d) (p (q d)) (p (p (q d))) at h
    simpa only [hab] using h
  · have h := hq.eq_swap_mul_swap_iff_mem_support.mpr hdq
    change q=cycle d (q d) (q (q d)) at h
    exact h.trans (cycle_rotate d (q d) (q (q d)) (by grind) (by grind) (by grind))

end SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleGeometry
