import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingMaximalCliques

/-! Every full coordinate-axis pullback is maximal, with no collapse
of the original fibres. This supplies all three genuine local cliques. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins
variable {A B C X : Type*} [Nontrivial A] [Nontrivial B] [Nontrivial C]

theorem pullback_firstAxis_maximal (f : X → A × (B × C)) (hf : Function.Surjective f)
    (b : B) (c : C) : MaximalPullbackClique f (f ⁻¹' FirstAxis b c) := by
  classical
  refine ⟨pullback_firstAxis_clique f b c, ?_⟩
  intro T hT hST x hx
  let a : A := Classical.arbitrary A
  obtain ⟨a', ha'⟩ := exists_ne a
  obtain ⟨u, hu⟩ := hf (a, (b, c))
  obtain ⟨v, hv⟩ := hf (a', (b, c))
  have huS : u ∈ f ⁻¹' FirstAxis b c := by change _ ∧ _; rw [hu]; exact ⟨rfl, rfl⟩
  have hvS : v ∈ f ⁻¹' FirstAxis b c := by change _ ∧ _; rw [hv]; exact ⟨rfl, rfl⟩
  have hxu := hT x hx u (hST huS)
  have hxv := hT x hx v (hST hvS)
  rw [hu] at hxu
  rw [hv] at hxv
  exact common_neighbors_first_difference (a, (b, c)) (a', (b, c)) (f x)
    (Ne.symm ha') (Or.inr (Or.inr ⟨rfl, rfl⟩)) hxu hxv

theorem pullback_secondAxis_maximal (f : X → A × (B × C)) (hf : Function.Surjective f)
    (a : A) (c : C) : MaximalPullbackClique f (f ⁻¹' SecondAxis a c) := by
  classical
  refine ⟨pullback_secondAxis_clique f a c, ?_⟩
  intro T hT hST x hx
  let b : B := Classical.arbitrary B
  obtain ⟨b', hb'⟩ := exists_ne b
  obtain ⟨u, hu⟩ := hf (a, (b, c))
  obtain ⟨v, hv⟩ := hf (a, (b', c))
  have huS : u ∈ f ⁻¹' SecondAxis a c := by change _ ∧ _; rw [hu]; exact ⟨rfl, rfl⟩
  have hvS : v ∈ f ⁻¹' SecondAxis a c := by change _ ∧ _; rw [hv]; exact ⟨rfl, rfl⟩
  have hxu := hT x hx u (hST huS)
  have hxv := hT x hx v (hST hvS)
  rw [hu] at hxu
  rw [hv] at hxv
  exact common_neighbors_first_difference (b, (a, c)) (b', (a, c))
    ((f x).2.1, ((f x).1, (f x).2.2)) (Ne.symm hb')
    (Or.inr (Or.inr ⟨rfl, rfl⟩))
    ((twoCoordinates_swap01 _ _).mpr hxu) ((twoCoordinates_swap01 _ _).mpr hxv)

theorem pullback_thirdAxis_maximal (f : X → A × (B × C)) (hf : Function.Surjective f)
    (a : A) (b : B) : MaximalPullbackClique f (f ⁻¹' ThirdAxis a b) := by
  classical
  refine ⟨pullback_thirdAxis_clique f a b, ?_⟩
  intro T hT hST x hx
  let c : C := Classical.arbitrary C
  obtain ⟨c', hc'⟩ := exists_ne c
  obtain ⟨u, hu⟩ := hf (a, (b, c))
  obtain ⟨v, hv⟩ := hf (a, (b, c'))
  have huS : u ∈ f ⁻¹' ThirdAxis a b := by change _ ∧ _; rw [hu]; exact ⟨rfl, rfl⟩
  have hvS : v ∈ f ⁻¹' ThirdAxis a b := by change _ ∧ _; rw [hv]; exact ⟨rfl, rfl⟩
  have hxu := hT x hx u (hST huS)
  have hxv := hT x hx v (hST hvS)
  rw [hu] at hxu
  rw [hv] at hxv
  have hh := common_neighbors_first_difference (c, (b, a)) (c', (b, a))
    ((f x).2.2, ((f x).2.1, (f x).1)) (Ne.symm hc')
    (Or.inr (Or.inr ⟨rfl, rfl⟩))
    ((twoCoordinates_swap02 _ _).mpr hxu) ((twoCoordinates_swap02 _ _).mpr hxv)
  exact ⟨hh.2, hh.1⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins
