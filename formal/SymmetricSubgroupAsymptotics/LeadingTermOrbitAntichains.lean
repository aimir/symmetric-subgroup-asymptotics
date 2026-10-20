import SymmetricSubgroupAsymptotics.LeadingTermMinimalGenerators
import Mathlib.Order.Antichain

/-! The orbit-colour part of the leading-coefficient argument: each
coefficient orbit contributes one antichain to a minimum-weight generating
tuple. All cancellation is in the original module. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.LeadingTermMinimalGenerators

variable {R M I C : Type} [Ring R] [AddCommGroup M] [Module R M]

/-- Minimum-weight generators have no comparable pair of the same colour
whenever the genuine module action can cancel such a pair. -/
theorem exists_generators_orbit_antichains
    (n : ℕ) (hn : ModuleGeneratedBy R M n) (weight : M → ℕ)
    (rel : I → I → Prop) (label : M → I) (colour : M → C)
    (hcancel : ∀ x y : M, x≠0 → y≠0 → rel (label x) (label y) →
      colour x=colour y → ∃ r : R, weight (y-r • x)<weight y) :
    ∃ v : Fin n → M, Submodule.span R (Set.range v)=⊤ ∧
      ∀ i j : Fin n, i≠j → v i≠0 → v j≠0 → colour (v i)=colour (v j) →
        ¬rel (label (v i)) (label (v j)) := by
  obtain ⟨v,hv,hmin⟩ := exists_minimum_weight n hn weight
  refine ⟨v,hv,?_⟩
  intro i j hij hi hj hc hr
  obtain ⟨r,hr⟩ := hcancel (v i) (v j) hi hj hr hc
  exact no_lower_weight_cancellation n weight v hv hmin j i hij r hr

/-- Count all nonzero tuple entries from their original height labels and
orbit colours. A colour fibre embeds in the height poset, and its image
is an antichain. -/
theorem nonzero_card_le_colours_mul_width
    [Fintype C] (n : ℕ) (v : Fin n → M)
    (rel : I → I → Prop) (hrefl : ∀ i, rel i i)
    (label : M → I) (colour : M → C) (w : ℕ)
    (hwidth : ∀ s : Finset I, IsAntichain rel (s : Set I) → s.card≤w)
    (hanti : ∀ i j : Fin n, i≠j → v i≠0 → v j≠0 →
      colour (v i)=colour (v j) → ¬rel (label (v i)) (label (v j))) :
    (Finset.univ.filter (fun i => v i≠0)).card≤Fintype.card C*w := by
  let s : Finset (Fin n) := Finset.univ.filter (fun i => v i≠0)
  have hfiber (c : C) : (s.filter (fun i => colour (v i)=c)).card≤w := by
    let t := s.filter (fun i => colour (v i)=c)
    have hprops {i : Fin n} (hi : i∈t) : v i≠0 ∧ colour (v i)=c := by
      obtain ⟨his,hic⟩ := Finset.mem_filter.mp hi
      exact ⟨(Finset.mem_filter.mp his).2,hic⟩
    have hinj : Set.InjOn (fun i => label (v i)) (t : Set (Fin n)) := by
      intro i hi j hj he
      change label (v i)=label (v j) at he
      by_contra hij
      exact hanti i j hij (hprops hi).1 (hprops hj).1
        ((hprops hi).2.trans (hprops hj).2.symm) (by rw [he]; exact hrefl _)
    have himage : IsAntichain rel (t.image (fun i => label (v i)) : Set I) := by
      intro a ha b hb hab hr
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
      have hij : i≠j := fun h => hab (congrArg (fun z => label (v z)) h)
      exact hanti i j hij (hprops hi).1 (hprops hj).1
        ((hprops hi).2.trans (hprops hj).2.symm) hr
    calc
      t.card=(t.image (fun i => label (v i))).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ w := hwidth _ himage
  have hpartition : s.card=∑ c : C, (s.filter (fun i => colour (v i)=c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  calc
    s.card=∑ c : C, (s.filter (fun i => colour (v i)=c)).card := hpartition
    _ ≤ ∑ _c : C, w := Finset.sum_le_sum (fun c _ => hfiber c)
    _ = Fintype.card C*w := by simp [Nat.mul_comm]

/-- The leading-term orbit method gives an actual finite generating set,
with the local orbit coefficient and poset width charged once each. -/
theorem exists_generating_finset_le_colours_mul_width
    [Fintype C] (n : ℕ) (hn : ModuleGeneratedBy R M n) (weight : M → ℕ)
    (rel : I → I → Prop) (hrefl : ∀ i, rel i i)
    (label : M → I) (colour : M → C) (w : ℕ)
    (hwidth : ∀ s : Finset I, IsAntichain rel (s : Set I) → s.card≤w)
    (hcancel : ∀ x y : M, x≠0 → y≠0 → rel (label x) (label y) →
      colour x=colour y → ∃ r : R, weight (y-r • x)<weight y) :
    ∃ S : Finset M, Submodule.span R (S : Set M)=⊤ ∧ S.card≤Fintype.card C*w := by
  obtain ⟨v,hv,hanti⟩ := exists_generators_orbit_antichains n hn weight rel label colour hcancel
  let s : Finset (Fin n) := Finset.univ.filter (fun i => v i≠0)
  let S := s.image v
  have hspan : Submodule.span R (S : Set M)=⊤ := by
    apply top_unique
    rw [←hv]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hi : v i=0
    · rw [hi]; exact Submodule.zero_mem _
    · exact Submodule.subset_span (Finset.mem_image.mpr
        ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩)
  exact ⟨S,hspan,Finset.card_image_le.trans
    (nonzero_card_le_colours_mul_width n v rel hrefl label colour w hwidth hanti)⟩

end SymmetricSubgroupAsymptotics.LeadingTermMinimalGenerators
