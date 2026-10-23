import Mathlib.GroupTheory.IsSubnormal
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.GroupAction.CardCommute
import Lean.Elab.Tactic.Omega

/-! Subnormal groups across an actual simple normal subgroup of index
two. The intersection is either trivial or the whole simple subgroup;
the small-quotient case retains its actual faithful quotient image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlmostSimpleIndexTwoSubnormalClasses
variable {G:Type*}[Group G][Finite G]

theorem containing_simple_index_two (N H:Subgroup G)(hindex:N.index=2)(hNH:N≤H) : H=N ∨ H=⊤ := by
  have hd:H.index∣2 := hindex ▸ Subgroup.index_dvd_of_le hNH
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1|h2
  · exact Or.inr (Subgroup.index_eq_one.mp h1)
  · apply Or.inl
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge hNH
    have hn:=N.card_mul_index
    have hh:=H.card_mul_index
    rw [hindex] at hn
    rw [h2] at hh
    omega

theorem subnormal_trichotomy (N:Subgroup G)[N.Normal][IsSimpleGroup N]
    (hindex:N.index=2)(H:Subgroup G)(hH:H.IsSubnormal) :
    Nat.card H≤2 ∨ H=N ∨ H=⊤ := by
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup
    (inferInstance:IsSimpleGroup N) (hH.subgroupOf : (H.subgroupOf N).IsSubnormal) with hb|ht
  · left
    let f:H→*G⧸N := (QuotientGroup.mk' N).comp H.subtype
    have hf:Function.Injective f := by
      apply f.ker_eq_bot_iff.mp
      apply le_antisymm _ bot_le
      intro g hg
      have hgN:g.val∈N := (QuotientGroup.eq_one_iff g.val).mp hg
      have hmem:(⟨g.val,hgN⟩:N)∈H.subgroupOf N := g.property
      rw [hb] at hmem
      have hz:(⟨g.val,hgN⟩:N)=1 := Subgroup.mem_bot.mp hmem
      have hv:g.val=1 := congrArg (fun z:N=>(z:G)) hz
      exact Subtype.ext hv
    have hc:=Nat.card_le_card_of_injective f hf
    simpa only [←Subgroup.index_eq_card,hindex] using hc
  · exact Or.inr (containing_simple_index_two N H hindex (Subgroup.subgroupOf_eq_top.mp ht))

theorem subnormal_class_card_le (N:Subgroup G)[N.Normal][IsSimpleGroup N]
    (hindex:N.index=2)(H:Subgroup G)(hH:H.IsSubnormal) :
    Nat.card (ConjClasses H)≤max 2 (max (Nat.card (ConjClasses N)) (Nat.card (ConjClasses G))) := by
  rcases subnormal_trichotomy N hindex H hH with hs|rfl|ht
  · exact ((Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective).trans hs).trans (Nat.le_max_left _ _)
  · exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  · subst H
    have he:Nat.card (ConjClasses (⊤:Subgroup G))≤Nat.card (ConjClasses G) :=
      Nat.card_le_card_of_surjective
        (ConjClasses.map (Subgroup.topEquiv:(⊤:Subgroup G)≃*G).symm.toMonoidHom)
        (ConjClasses.map_surjective (Subgroup.topEquiv:(⊤:Subgroup G)≃*G).symm.surjective)
    exact he.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

theorem alternating_subnormal_trichotomy (m:ℕ)(hm:5≤m)
    (H:Subgroup (Equiv.Perm (Fin m)))(hH:H.IsSubnormal) :
    Nat.card H≤2 ∨ H=alternatingGroup (Fin m) ∨ H=⊤ := by
  letI : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup (by simpa using hm)
  letI : Nontrivial (Fin m) := Finite.one_lt_card_iff_nontrivial.mp (by simp only [Nat.card_fin];omega)
  exact subnormal_trichotomy _ alternatingGroup.index_eq_two H hH

end SymmetricSubgroupAsymptotics.AlmostSimpleIndexTwoSubnormalClasses
