import SymmetricSubgroupAsymptotics.CFSGPrimeTranslationNormalRecurrence
import SymmetricSubgroupAsymptotics.PermutationPrimeGroupRank

/-! A classification-free normal-rank bound in odd-prime transitive
permutation groups. It concerns the normal generators under the entire
original group; normal subgroups need not act transitively. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPrimeTransitiveNormalBound

/-- The central prime-frame recurrence before numerical simplification. -/
def bound (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k+2 => bound p (k+1)+p^k

/-- All original normal subgroups, including proper ones, satisfy this
uniform recurrence. There is no action registry or finite-case premise. -/
theorem normalGen_le_bound (p : ℕ) [Fact p.Prime] (k : ℕ)
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup p U) (hdegree : Nat.card X=p^k)
    (N : Subgroup U) [N.Normal] : MarkedC4.normalGen N≤bound p k := by
  induction k generalizing X with
  | zero =>
    letI : Subsingleton X := Finite.card_le_one_iff_subsingleton.mp (by simpa using hdegree.le)
    letI : Subsingleton U := ⟨fun a b => eq_of_smul_eq_smul (α := X)
      (fun x => Subsingleton.elim (a • x) (b • x))⟩
    have hN : N=⊥ := Subsingleton.elim _ _
    rw [hN,MarkedC4.normalGen_bot]
    rfl
  | succ k ih =>
    have hp : p.Prime := Fact.out
    have hcard : 1<Nat.card X := by
      rw [hdegree]
      exact one_lt_pow' hp.one_lt (by omega)
    letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp hcard
    have hnt : Nontrivial U := by
      obtain ⟨x,y,hxy⟩ := exists_pair_ne X
      obtain ⟨u,hu⟩ := MulAction.exists_smul_eq U x y
      refine ⟨⟨u,1,fun h => hxy ?_⟩⟩
      rw [←hu,h,one_smul]
    obtain ⟨z,hz,hzp⟩ := CentralPrimeFrame.exists_central_order U hU hnt
    let F := CentralPrimeFrame.translationFrame z hz hzp
    letI : MulAction U (CentralPrimeFrame.Blocks z) :=
      MulAction.compHom _ (CentralPrimeFrame.topHom z hz)
    have hact : ∀ (u : U) (i : CentralPrimeFrame.Blocks z),u • i=F.top u i := fun _ _ => rfl
    have hI : Nat.card (CentralPrimeFrame.Blocks z)=p^k := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      have h := CentralPrimeFrame.card_blocks z hz hzp
      rw [hdegree,pow_succ'] at h
      exact h
    cases k with
    | zero =>
      letI : Subsingleton (CentralPrimeFrame.Blocks z) :=
        Finite.card_le_one_iff_subsingleton.mp (by simpa using hI.le)
      have hNK : N≤F.top.ker := by
        intro n _
        exact Subsingleton.elim (F.top n) 1
      have h := F.normalGen_le_card hact hU N hNK
      simpa only [hI,pow_zero,bound] using h
    | succ k =>
      letI : Nontrivial (CentralPrimeFrame.Blocks z) :=
        Finite.one_lt_card_iff_nontrivial.mp (by
          rw [hI]
          exact one_lt_pow' hp.one_lt (by omega))
      letI : MulAction.IsPretransitive U (CentralPrimeFrame.Blocks z) :=
        ⟨fun i j => CentralPrimeFrame.topHom_transitive z hz i j⟩
      letI : MulAction.IsPretransitive F.top.range (CentralPrimeFrame.Blocks z) := by
        constructor
        intro i j
        obtain ⟨u,hu⟩ := MulAction.exists_smul_eq U i j
        exact ⟨F.top.rangeRestrict u,hu⟩
      have hTop : IsPGroup p F.top.range :=
        hU.of_surjective F.top.rangeRestrict F.top.rangeRestrict_surjective
      letI : (N.map F.top.rangeRestrict).Normal :=
        Subgroup.Normal.map inferInstance F.top.rangeRestrict F.top.rangeRestrict_surjective
      have ht := ih F.top.range hTop hI (N.map F.top.rangeRestrict)
      have h := F.normalGen_le_div_add_actual_image hact hU N
      have hdiv : Nat.card (CentralPrimeFrame.Blocks z)/p=p^k := by
        rw [hI,pow_succ,Nat.mul_div_cancel _ hp.pos]
      rw [hdiv] at h
      change MarkedC4.normalGen N≤bound p (k+1)+p^k
      omega

/-- In degree p^(k+2), the uniform bound is at most 2*p^k. -/
theorem bound_le_twice_power {p : ℕ} (hp : 2≤p) (k : ℕ) :
    bound p (k+2)≤2*p^k := by
  induction k with
  | zero => simp [bound]
  | succ k ih =>
    change bound p (k+2)+p^(k+1)≤2*p^(k+1)
    rw [pow_succ]
    have hm := Nat.mul_le_mul_right (p^k) hp
    nlinarith

/-- The odd-prime normal-generator estimate used in RDT5.3(iii), with no
new published input. The proof actually works for every prime. -/
theorem normalGen_le_twice_power (p : ℕ) [Fact p.Prime] (k : ℕ)
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup p U)
    (hdegree : Nat.card X=p^(k+2)) (N : Subgroup U) [N.Normal] :
    MarkedC4.normalGen N≤2*p^k :=
  (normalGen_le_bound p (k+2) U hU hdegree N).trans
    (bound_le_twice_power (Fact.out : p.Prime).two_le k)

end SymmetricSubgroupAsymptotics.CFSGPrimeTransitiveNormalBound
