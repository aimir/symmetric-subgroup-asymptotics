import SymmetricSubgroupAsymptotics.OrdinaryRemainderAssembly

/-!
# The literal odd critical branch

This exposes membership in the parity-defined critical family at odd degree
as membership in the already assembled literal odd family.  Downstream
physical ownership arguments can therefore use their actual subgroups
without carrying a dependent parity cast.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

universe u v

private theorem embedding_cast_apply {A B : Type u} {X : Type v} (h : A = B)
    (j : B ↪ X) (a : A) :
    (Eq.mpr (congrArg (fun T => T ↪ X) h) j) a = j (Eq.mp h a) := by
  cases h
  rfl

private theorem eq_mp_mpr_apply {A B : Type u} (h : A = B) (b : B) :
    Eq.mp h (Eq.mpr h b) = b := by
  cases h
  rfl

private theorem criticalSubgroupEmbedding_odd_raw (N : ℕ)
    (K : CriticalSubgroups (2*N+1)) :
    ∃ J : OddCriticalSubgroupsOn ((2*N+1)/2) (2*N+1),
      J.val = criticalSubgroupEmbedding (2*N+1) K := by
  have hn : ¬ (2*N+1) % 2 = 0 := by omega
  have hdec : instDecidableEqNat ((2*N+1) % 2) 0 = Decidable.isFalse hn :=
    Subsingleton.elim _ _
  let j : OddCriticalSubgroupsOn ((2*N+1)/2) (2*N+1) ↪
      Subgroup (Equiv.Perm (Fin (2*N+1))) :=
    ⟨Subtype.val,Subtype.val_injective⟩
  have h := embedding_cast_apply (if_neg hn) j K
  refine ⟨Eq.mp (if_neg hn) K,?_⟩
  simp only [criticalSubgroupEmbedding,CriticalSubgroups,hdec]
  exact h.symm

private theorem oddCriticalSubgroupsOn_mp_val {R S n : ℕ} (h : R = S)
    (J : OddCriticalSubgroupsOn R n) :
    (Eq.mp (congrArg (fun T => OddCriticalSubgroupsOn T n) h) J).val = J.val := by
  cases h
  rfl

theorem criticalSubgroupEmbedding_odd_exists (N : ℕ)
    (K : CriticalSubgroups (2*N+1)) :
    ∃ J : OddCriticalSubgroups N,
      J.val = criticalSubgroupEmbedding (2*N+1) K := by
  obtain ⟨J,hJ⟩ := criticalSubgroupEmbedding_odd_raw N K
  have hhalf : (2*N+1)/2 = N := by omega
  let J' : OddCriticalSubgroups N :=
    Eq.mp (congrArg (fun R => OddCriticalSubgroupsOn R (2*N+1)) hhalf) J
  refine ⟨J',?_⟩
  exact (oddCriticalSubgroupsOn_mp_val hhalf J).trans hJ

private theorem oddCriticalSubgroupsOn_mpr_val {R S n : ℕ} (h : R = S)
    (J : OddCriticalSubgroupsOn S n) :
    (Eq.mpr (congrArg (fun T => OddCriticalSubgroupsOn T n) h) J).val = J.val := by
  cases h
  rfl

theorem oddCriticalSubgroup_has_embedding (N : ℕ) (J : OddCriticalSubgroups N) :
    ∃ K : CriticalSubgroups (2*N+1),
      criticalSubgroupEmbedding (2*N+1) K = J.val := by
  have hn : ¬ (2*N+1) % 2 = 0 := by omega
  have hdec : instDecidableEqNat ((2*N+1) % 2) 0 = Decidable.isFalse hn :=
    Subsingleton.elim _ _
  have hhalf : (2*N+1)/2 = N := by omega
  let hB := congrArg
    (fun R => OddCriticalSubgroupsOn R (2*N+1)) hhalf
  let J0 : OddCriticalSubgroupsOn ((2*N+1)/2) (2*N+1) := Eq.mpr hB J
  let j : OddCriticalSubgroupsOn ((2*N+1)/2) (2*N+1) ↪
      Subgroup (Equiv.Perm (Fin (2*N+1))) :=
    ⟨Subtype.val,Subtype.val_injective⟩
  let K : CriticalSubgroups (2*N+1) := Eq.mpr (if_neg hn) J0
  refine ⟨K,?_⟩
  have h := embedding_cast_apply (if_neg hn) j K
  simp only [criticalSubgroupEmbedding,CriticalSubgroups,hdec]
  calc
    _ = j (Eq.mp (if_neg hn) K) := h
    _ = j J0 := by
      apply congrArg j
      exact eq_mp_mpr_apply (if_neg hn) J0
    _ = J0.val := rfl
    _ = J.val := oddCriticalSubgroupsOn_mpr_val hhalf J

theorem isCriticalSubgroup_odd_iff (N : ℕ)
    (H : Subgroup (Equiv.Perm (Fin (2*N+1)))) :
    IsCriticalSubgroup (2*N+1) H ↔
      ∃ J : OddCriticalSubgroups N, J.val = H := by
  simp only [IsCriticalSubgroup,Set.mem_range]
  constructor
  · rintro ⟨K,hK⟩
    obtain ⟨J,hJ⟩ := criticalSubgroupEmbedding_odd_exists N K
    exact ⟨J,hJ.trans hK⟩
  · rintro ⟨J,hJ⟩
    obtain ⟨K,hK⟩ := oddCriticalSubgroup_has_embedding N J
    exact ⟨K,hK.trans hJ⟩

end SymmetricSubgroupAsymptotics

end
