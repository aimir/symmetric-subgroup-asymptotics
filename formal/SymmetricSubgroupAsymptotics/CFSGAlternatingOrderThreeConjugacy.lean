import SymmetricSubgroupAsymptotics.CFSGAlternatingOrderThreeCentralizers

/-! Order-three cycle types do not split into two alternating-group
conjugacy classes: their symmetric centralizer contains an odd element. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingOrderThreeConjugacy
open Equiv Equiv.Perm CFSGAlternatingOrderThreeCentralizers

/-- An odd centralizing permutation corrects the parity of an actual
point conjugator without changing its conjugacy equation. -/
theorem isConj_of_odd_centralizer {α : Type*} [Fintype α] [DecidableEq α]
    (p q : alternatingGroup α) (hc : IsConj p.val q.val)
    (hodd : ¬Subgroup.centralizer ({p.val} : Set (Perm α))≤alternatingGroup α) : IsConj p q := by
  obtain ⟨σ,hσ⟩ := isConj_iff.mp hc
  rcases Int.units_eq_one_or (Perm.sign σ) with hs|hs
  · apply isConj_iff.mpr
    refine ⟨⟨σ,Perm.mem_alternatingGroup.mpr hs⟩,Subtype.ext ?_⟩
    exact hσ
  · obtain ⟨c,hc,hcn⟩ : ∃ c,c∈Subgroup.centralizer ({p.val} : Set (Perm α)) ∧
        c∉alternatingGroup α := by
      by_contra h
      apply hodd
      intro c hc
      by_contra hcn
      exact h ⟨c,hc,hcn⟩
    have hcs : Perm.sign c = -1 := (Int.units_eq_one_or (Perm.sign c)).resolve_left
      (fun h => hcn (Perm.mem_alternatingGroup.mpr h))
    have hcp := Subgroup.mem_centralizer_singleton_iff.mp hc
    apply isConj_iff.mpr
    refine ⟨⟨σ*c,?_⟩,Subtype.ext ?_⟩
    · apply Perm.mem_alternatingGroup.mpr
      rw [map_mul,hs,hcs,Int.units_mul_self]
    · change (σ*c)*p.val*(σ*c)⁻¹=q.val
      rw [mul_inv_rev]
      calc
        (σ*c)*p.val*(c⁻¹*σ⁻¹) = σ*(c*p.val*c⁻¹)*σ⁻¹ := by simp only [mul_assoc]
        _ = σ*p.val*σ⁻¹ := by rw [hcp];simp only [mul_assoc,mul_inv_cancel,mul_one]
        _ = q.val := hσ

/-- In every degree at least five, equal order-three profiles give
conjugacy inside the literal alternating group, not merely inside S_n. -/
theorem isConj_of_three_cycle_type (n : ℕ) (hn : 5≤n)
    (p q : alternatingGroup (Fin n)) (k : ℕ) (hk : 1≤k)
    (hp : p.val.cycleType=Multiset.replicate k 3)
    (hq : q.val.cycleType=Multiset.replicate k 3) : IsConj p q := by
  apply isConj_of_odd_centralizer p q
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr (hp.trans hq.symm))
  exact centralizer_not_le_alternating_of_type n hn p.val k hk hp

end SymmetricSubgroupAsymptotics.CFSGAlternatingOrderThreeConjugacy
