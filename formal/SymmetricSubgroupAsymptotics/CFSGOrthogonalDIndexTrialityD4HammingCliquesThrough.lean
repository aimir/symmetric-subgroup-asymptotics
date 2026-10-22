import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingAxisMaximality

/-! Through every original pullback vertex pass exactly the three
full coordinate-axis cliques; the three sets are genuinely distinct. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins
variable {A B C X : Type*} [Nontrivial A] [Nontrivial B] [Nontrivial C]

theorem maximal_pullback_eq_axis_at (f : X → A × (B × C)) (hf : Function.Surjective f)
    (S : Set X) (hS : MaximalPullbackClique f S) (x : X) (hx : x ∈ S) :
    S = f ⁻¹' FirstAxis (f x).2.1 (f x).2.2 ∨
      S = f ⁻¹' SecondAxis (f x).1 (f x).2.2 ∨
      S = f ⁻¹' ThirdAxis (f x).1 (f x).2.1 := by
  obtain ⟨a, _, ha | ha | ha⟩ := maximal_pullback_eq_axis f hf S hS
  · have hh : (f x).2.1 = (f a).2.1 ∧ (f x).2.2 = (f a).2.2 := by
      have hx' : x ∈ f ⁻¹' FirstAxis (f a).2.1 (f a).2.2 := by
        rw [← ha]
        exact hx
      exact hx' 
    exact Or.inl (by simpa only [hh.1, hh.2] using ha)
  · have hh : (f x).1 = (f a).1 ∧ (f x).2.2 = (f a).2.2 := by
      have hx' : x ∈ f ⁻¹' SecondAxis (f a).1 (f a).2.2 := by
        rw [← ha]
        exact hx
      exact hx' 
    exact Or.inr (Or.inl (by simpa only [hh.1, hh.2] using ha))
  · have hh : (f x).1 = (f a).1 ∧ (f x).2.1 = (f a).2.1 := by
      have hx' : x ∈ f ⁻¹' ThirdAxis (f a).1 (f a).2.1 := by
        rw [← ha]
        exact hx
      exact hx' 
    exact Or.inr (Or.inr (by simpa only [hh.1, hh.2] using ha))

omit [Nontrivial C] in
theorem axes_through_distinct (f : X → A × (B × C)) (hf : Function.Surjective f) (x : X) :
    (f ⁻¹' FirstAxis (f x).2.1 (f x).2.2 ≠ f ⁻¹' SecondAxis (f x).1 (f x).2.2) ∧
    (f ⁻¹' FirstAxis (f x).2.1 (f x).2.2 ≠ f ⁻¹' ThirdAxis (f x).1 (f x).2.1) ∧
    (f ⁻¹' SecondAxis (f x).1 (f x).2.2 ≠ f ⁻¹' ThirdAxis (f x).1 (f x).2.1) := by
  classical
  obtain ⟨a, ha⟩ := exists_ne (f x).1
  obtain ⟨b, hb⟩ := exists_ne (f x).2.1
  obtain ⟨y, hy⟩ := hf (a, ((f x).2.1, (f x).2.2))
  obtain ⟨z, hz⟩ := hf ((f x).1, (b, (f x).2.2))
  have hyFirst : y ∈ f ⁻¹' FirstAxis (f x).2.1 (f x).2.2 := by
    change _ ∧ _
    rw [hy]
    exact ⟨rfl, rfl⟩
  have hzSecond : z ∈ f ⁻¹' SecondAxis (f x).1 (f x).2.2 := by
    change _ ∧ _
    rw [hz]
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hm : y ∈ f ⁻¹' SecondAxis (f x).1 (f x).2.2 := he ▸ hyFirst
    have hh : (f y).1 = (f x).1 := hm.1
    rw [hy] at hh
    exact ha hh
  · intro he
    have hm : y ∈ f ⁻¹' ThirdAxis (f x).1 (f x).2.1 := he ▸ hyFirst
    have hh : (f y).1 = (f x).1 := hm.1
    rw [hy] at hh
    exact ha hh
  · intro he
    have hm : z ∈ f ⁻¹' ThirdAxis (f x).1 (f x).2.1 := he ▸ hzSecond
    have hh : (f z).2.1 = (f x).2.1 := hm.2
    rw [hz] at hh
    exact hb hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingTwins
