import SymmetricSubgroupAsymptotics.OrdinaryRemainderAssembly

/-!
# The literal even critical branch

Membership in the parity-defined critical family at even degree is exposed
as membership in the already assembled literal even family.  The proof
retains the underlying physical subgroup through every dependent cast.
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

private theorem criticalSubgroupEmbedding_even_raw (N : ℕ)
    (K : CriticalSubgroups (2*N)) :
    ∃ J : EvenCriticalSubgroupsOn ((2*N)/2) (2*N),
      J.val = criticalSubgroupEmbedding (2*N) K := by
  have hn : (2*N) % 2 = 0 := by omega
  have hdec : instDecidableEqNat ((2*N) % 2) 0 = Decidable.isTrue hn :=
    Subsingleton.elim _ _
  let j : EvenCriticalSubgroupsOn ((2*N)/2) (2*N) ↪
      Subgroup (Equiv.Perm (Fin (2*N))) :=
    ⟨Subtype.val,Subtype.val_injective⟩
  have h := embedding_cast_apply (if_pos hn) j K
  refine ⟨Eq.mp (if_pos hn) K,?_⟩
  simp only [criticalSubgroupEmbedding,CriticalSubgroups,hdec]
  exact h.symm

private theorem evenCriticalSubgroupsOn_mp_val {R S n : ℕ} (h : R = S)
    (J : EvenCriticalSubgroupsOn R n) :
    (Eq.mp (congrArg (fun T => EvenCriticalSubgroupsOn T n) h) J).val = J.val := by
  cases h
  rfl

theorem criticalSubgroupEmbedding_even_exists (N : ℕ)
    (K : CriticalSubgroups (2*N)) :
    ∃ J : EvenCriticalSubgroups N,
      J.val = criticalSubgroupEmbedding (2*N) K := by
  obtain ⟨J,hJ⟩ := criticalSubgroupEmbedding_even_raw N K
  have hhalf : (2*N)/2 = N := by omega
  let J' : EvenCriticalSubgroups N :=
    Eq.mp (congrArg (fun R => EvenCriticalSubgroupsOn R (2*N)) hhalf) J
  refine ⟨J',?_⟩
  exact (evenCriticalSubgroupsOn_mp_val hhalf J).trans hJ

private theorem evenCriticalSubgroupsOn_mpr_val {R S n : ℕ} (h : R = S)
    (J : EvenCriticalSubgroupsOn S n) :
    (Eq.mpr (congrArg (fun T => EvenCriticalSubgroupsOn T n) h) J).val = J.val := by
  cases h
  rfl

theorem evenCriticalSubgroup_has_embedding (N : ℕ) (J : EvenCriticalSubgroups N) :
    ∃ K : CriticalSubgroups (2*N),
      criticalSubgroupEmbedding (2*N) K = J.val := by
  have hn : (2*N) % 2 = 0 := by omega
  have hdec : instDecidableEqNat ((2*N) % 2) 0 = Decidable.isTrue hn :=
    Subsingleton.elim _ _
  have hhalf : (2*N)/2 = N := by omega
  let hB := congrArg (fun R => EvenCriticalSubgroupsOn R (2*N)) hhalf
  let J0 : EvenCriticalSubgroupsOn ((2*N)/2) (2*N) := Eq.mpr hB J
  let j : EvenCriticalSubgroupsOn ((2*N)/2) (2*N) ↪
      Subgroup (Equiv.Perm (Fin (2*N))) :=
    ⟨Subtype.val,Subtype.val_injective⟩
  let K : CriticalSubgroups (2*N) := Eq.mpr (if_pos hn) J0
  refine ⟨K,?_⟩
  have h := embedding_cast_apply (if_pos hn) j K
  simp only [criticalSubgroupEmbedding,CriticalSubgroups,hdec]
  calc
    _ = j (Eq.mp (if_pos hn) K) := h
    _ = j J0 := by
      apply congrArg j
      exact eq_mp_mpr_apply (if_pos hn) J0
    _ = J0.val := rfl
    _ = J.val := evenCriticalSubgroupsOn_mpr_val hhalf J

theorem isCriticalSubgroup_even_iff (N : ℕ)
    (H : Subgroup (Equiv.Perm (Fin (2*N)))) :
    IsCriticalSubgroup (2*N) H ↔
      ∃ J : EvenCriticalSubgroups N, J.val = H := by
  simp only [IsCriticalSubgroup,Set.mem_range]
  constructor
  · rintro ⟨K,hK⟩
    obtain ⟨J,hJ⟩ := criticalSubgroupEmbedding_even_exists N K
    exact ⟨J,hJ.trans hK⟩
  · rintro ⟨J,hJ⟩
    obtain ⟨K,hK⟩ := evenCriticalSubgroup_has_embedding N J
    exact ⟨K,hK.trans hJ⟩

end SymmetricSubgroupAsymptotics

end
