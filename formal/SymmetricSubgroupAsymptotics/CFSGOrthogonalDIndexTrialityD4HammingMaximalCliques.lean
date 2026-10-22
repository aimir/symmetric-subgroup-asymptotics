import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingCliques

/-! Every maximal clique in a SURJECTIVE Hamming pullback is the full
inverse image of an actual coordinate axis. In particular the entire
twin fibre is retained. This is proved, not a maximal-clique callback. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins
variable {A B C X : Type*} [Nontrivial A] [Nontrivial B] [Nontrivial C]

def PullbackClique (f : X → A × (B × C)) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, TwoCoordinates (f x) (f y)

def MaximalPullbackClique (f : X → A × (B × C)) (S : Set X) : Prop :=
  PullbackClique f S ∧ ∀ T, PullbackClique f T → S ⊆ T → T ⊆ S

omit [Nontrivial A] [Nontrivial B] [Nontrivial C] in
theorem pullback_firstAxis_clique (f : X → A × (B × C)) (b : B) (c : C) :
    PullbackClique f (f ⁻¹' FirstAxis b c) :=
  fun x hx y hy => firstAxis_clique b c (f x) hx (f y) hy

omit [Nontrivial A] [Nontrivial B] [Nontrivial C] in
theorem pullback_secondAxis_clique (f : X → A × (B × C)) (a : A) (c : C) :
    PullbackClique f (f ⁻¹' SecondAxis a c) :=
  fun x hx y hy => secondAxis_clique a c (f x) hx (f y) hy

omit [Nontrivial A] [Nontrivial B] [Nontrivial C] in
theorem pullback_thirdAxis_clique (f : X → A × (B × C)) (a : A) (b : B) :
    PullbackClique f (f ⁻¹' ThirdAxis a b) :=
  fun x hx y hy => thirdAxis_clique a b (f x) hx (f y) hy

theorem maximal_pullback_eq_axis (f : X → A × (B × C)) (hf : Function.Surjective f)
    (S : Set X) (hS : MaximalPullbackClique f S) :
    ∃ a ∈ S, S = f ⁻¹' FirstAxis (f a).2.1 (f a).2.2 ∨
      S = f ⁻¹' SecondAxis (f a).1 (f a).2.2 ∨ S = f ⁻¹' ThirdAxis (f a).1 (f a).2.1 := by
  classical
  have hnon : S.Nonempty := by
    by_contra hn
    have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨x, hx⟩ := hf (Classical.arbitrary (A × (B × C)))
    have hsingle : PullbackClique f {x} := by
      rintro u rfl v rfl
      exact Or.inl ⟨rfl, rfl⟩
    have hm := hS.2 {x} hsingle (by rw [he]; exact Set.empty_subset _)
    have hxS := hm (show x ∈ ({x} : Set X) from rfl)
    simpa only [he, Set.mem_empty_iff_false] using hxS
  obtain ⟨a, ha⟩ := hnon
  have hex : ∃ b ∈ S, f a ≠ f b := by
    by_contra hn
    have he : ∀ b ∈ S, f b = f a := by
      intro b hb
      by_contra hne
      exact hn ⟨b, hb, Ne.symm hne⟩
    have hsub : S ⊆ f ⁻¹' FirstAxis (f a).2.1 (f a).2.2 := by
      intro b hb
      exact ⟨congrArg (fun p => p.2.1) (he b hb), congrArg (fun p => p.2.2) (he b hb)⟩
    have hm := hS.2 _ (pullback_firstAxis_clique f _ _) hsub
    obtain ⟨c, hc⟩ := exists_ne (f a).1
    obtain ⟨b, hb⟩ := hf (c, ((f a).2.1, (f a).2.2))
    have hbS : b ∈ S := hm ⟨congrArg (fun p => p.2.1) hb, congrArg (fun p => p.2.2) hb⟩
    have hh := congrArg Prod.fst ((hb.symm).trans (he b hbS))
    exact hc hh
  obtain ⟨b, hb, hne⟩ := hex
  have himage : CoordinateClique (f '' S) := by
    rintro u ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩
    exact hS.1 x hx y hy
  have haxes := clique_contained_axis (f '' S) himage (f a) (f b) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hne
  refine ⟨a, ha, ?_⟩
  rcases haxes with h0 | h1 | h2
  · have hs : S ⊆ f ⁻¹' FirstAxis (f a).2.1 (f a).2.2 :=
      fun x hx => h0 ⟨x, hx, rfl⟩
    exact Or.inl (Set.Subset.antisymm hs (hS.2 _ (pullback_firstAxis_clique f _ _) hs))
  · have hs : S ⊆ f ⁻¹' SecondAxis (f a).1 (f a).2.2 :=
      fun x hx => h1 ⟨x, hx, rfl⟩
    exact Or.inr (Or.inl (Set.Subset.antisymm hs (hS.2 _ (pullback_secondAxis_clique f _ _) hs)))
  · have hs : S ⊆ f ⁻¹' ThirdAxis (f a).1 (f a).2.1 :=
      fun x hx => h2 ⟨x, hx, rfl⟩
    exact Or.inr (Or.inr (Set.Subset.antisymm hs (hS.2 _ (pullback_thirdAxis_clique f _ _) hs)))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins
