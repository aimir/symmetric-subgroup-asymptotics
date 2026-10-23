import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Finite.Card
import Lean.Elab.Tactic.Omega

/-! The actual p-group generating-set bound: adjoining a new generator
increases the subgroup order by at least p. This works for every finite
p-group, without an elementary-abelian or nilpotency-class assumption. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PGroupGeneratingCardinality

theorem exists_generating_finset_prime_pow_le (p : ℕ) [hp : Fact p.Prime]
    (G : Type*) [Group G] [Finite G] (hG : IsPGroup p G) :
    ∃ S : Finset G, Subgroup.closure (S : Set G)=⊤ ∧ p^S.card ≤ Nat.card G := by
  suffices h : ∀ m : ℕ, ∀ S : Finset G,
      p^S.card ≤ Nat.card (Subgroup.closure (S : Set G)) →
      Nat.card G-Nat.card (Subgroup.closure (S : Set G)) ≤ m →
      ∃ T : Finset G, Subgroup.closure (T : Set G)=⊤ ∧ p^T.card ≤ Nat.card G by
    refine h (Nat.card G) ∅ ?_ (Nat.sub_le _ _)
    simp
  intro m
  induction m with
  | zero =>
    intro S hS hm
    have he : Nat.card (Subgroup.closure (S : Set G))=Nat.card G :=
      le_antisymm (Subgroup.card_le_card_group _) (by omega)
    exact ⟨S,Subgroup.eq_top_of_card_eq _ he,hS.trans he.le⟩
  | succ m ih =>
    intro S hS hm
    by_cases htop : Subgroup.closure (S : Set G)=⊤
    · exact ⟨S,htop,hS.trans (Subgroup.card_le_card_group _)⟩
    obtain ⟨g,hg⟩ : ∃ g, g ∉ Subgroup.closure (S : Set G) := by
      by_contra hall
      apply htop
      apply top_unique
      intro g _
      by_contra hg
      exact hall ⟨g,hg⟩
    have hgS : g ∉ S := fun hs => hg (Subgroup.subset_closure hs)
    let S' := insert g S
    have hle : Subgroup.closure (S : Set G) ≤ Subgroup.closure (S' : Set G) :=
      Subgroup.closure_mono (by simp [S'])
    have hgS' : g ∈ Subgroup.closure (S' : Set G) := Subgroup.subset_closure (by simp [S'])
    have hlt : Nat.card (Subgroup.closure (S : Set G)) <
        Nat.card (Subgroup.closure (S' : Set G)) := by
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) ?_
      intro he
      have heq := Subgroup.eq_of_le_of_card_ge hle he.ge
      exact hg (heq ▸ hgS')
    obtain ⟨a,ha⟩ := (hG.to_subgroup (Subgroup.closure (S : Set G))).exists_card_eq
    obtain ⟨b,hb⟩ := (hG.to_subgroup (Subgroup.closure (S' : Set G))).exists_card_eq
    have hab : a < b := (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp (by
      rw [←ha,←hb]
      exact hlt)
    have hfold : p*Nat.card (Subgroup.closure (S : Set G)) ≤
        Nat.card (Subgroup.closure (S' : Set G)) := by
      calc
        p*Nat.card (Subgroup.closure (S : Set G)) = p^(a+1) := by
          rw [ha,pow_succ,Nat.mul_comm]
        _ ≤ p^b := Nat.pow_le_pow_right hp.out.pos (by omega)
        _ = Nat.card (Subgroup.closure (S' : Set G)) := hb.symm
    apply ih S'
    · rw [show S'.card=S.card+1 from Finset.card_insert_of_notMem hgS,pow_succ]
      exact (Nat.mul_le_mul_right p hS).trans (by simpa only [Nat.mul_comm] using hfold)
    · have hcard := Subgroup.card_le_card_group (Subgroup.closure (S' : Set G))
      omega

end SymmetricSubgroupAsymptotics.PGroupGeneratingCardinality
