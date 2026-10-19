import SymmetricSubgroupAsymptotics.MarkedC4ActualExcessOneQuotientRank

/-! An actual failure of the quotient normal quarter bound supplies the
ordinary excessive target packet. Only exact ordinary RDT5.3/5.7 inputs
are invoked; no marked count or target-invariant capacity is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualCaseIITargetStructure
open RDTExcessStructure ActualNormalFMarkedPeel

/-- The portions of ordinary RDT5.3(i) needed for target selection. -/
def PublishedProposition53Binary : Prop :=
  ∀ (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))),2<n →IsPGroup 2 G →
    (∀ x y : Fin n,∃ g : G,g.val x=y) →
    (∃ U : Subgroup G,U.Normal ∧ (n : ℝ)/4<(normalGen U : ℝ)) →
    ∃ i : ℕ,(i=1 ∨ i=2) ∧ HasExcess G n i ∧ n≤32 ∧
      (i=1 →∀ U : Subgroup G,U.Normal →(n : ℝ)/4<(normalGen U : ℝ) →U=⊤) ∧
      (i=2 →n=8 ∨ n=16 ∨ n=32)

theorem exists_actual_target_packet
    (h53 : PublishedProposition53Binary) (h57 : PublishedTheorem57Binary)
    (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) (hn : 2<n) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin n,∃ g : G,g.val x=y)
    (N : Subgroup G) [N.Normal] (hnonab : ¬∀ x y : G ⧸ N,x*y=y*x)
    (V : Subgroup (G ⧸ N)) [V.Normal] (hV : (n : ℝ)/4<(normalGen V : ℝ)) :
    ∃ (i : ℕ) (F : Subgroup (G ⧸ N)) (e : ℝ),
      (i=1 ∨ i=2) ∧ HasExcess G n i ∧ n≤32 ∧ F.Normal ∧
      ((i=2 ∧ n=8 ∧ N=⊥ ∧ F=⊤ ∧ e=3) ∨ (i=1 ∧ e=1) ∨ (i=2 ∧ e=5/4)) ∧
      commutatorLog F+e*centralLog F≤(n : ℝ)/2 ∧ centralLog F≤(n : ℝ)/4 := by
  let q := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hmap : (V.comap q).map q=V := by
    apply Subgroup.map_comap_eq_self
    rw [q.range_eq_top_of_surjective hq]
    exact le_top
  have hnormal : normalGen V≤normalGen (V.comap q) := by
    have h := normalGen_map_le q hq (V.comap q)
    rw [hmap] at h
    exact h
  have hreal : (normalGen V : ℝ)≤normalGen (V.comap q) := by exact_mod_cast hnormal
  obtain ⟨i,hi,hexcess,hdegree,honly,hdegree2⟩ :=
    h53 n G hn hG htrans ⟨V.comap q,inferInstance,lt_of_lt_of_le hV hreal⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Group.IsNilpotent G := hG.isNilpotent
  have hrank : i=1 →genRank (G ⧸ N)=genRank G := by
    intro hi1
    exact ActualExcessOneQuotientRank.quotient_rank_eq q hq n
      (hi1 ▸ hexcess) (honly hi1) V hV
  obtain ⟨F,e,hFn,hbranch,hbound,hcentral⟩ :=
    h57 n G hn hG htrans i hi hexcess N hnonab hrank
  exact ⟨i,F,e,hi,hexcess,hdegree,hFn,hbranch,hbound,hcentral⟩

end SymmetricSubgroupAsymptotics.MarkedC4.ActualCaseIITargetStructure
