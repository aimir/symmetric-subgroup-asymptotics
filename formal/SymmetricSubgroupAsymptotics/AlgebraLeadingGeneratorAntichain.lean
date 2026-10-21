import SymmetricSubgroupAsymptotics.AlgebraOperatorLeadingGeneratorBound

/-! A minimum-weight generating tuple retains an actual leading antichain.
This exposes the original generators rather than just their cardinal bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

variable {k A M : Type} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    {n d : ℕ}

theorem algebra_generating_finset_with_leading_antichain
    (hd : ModuleGeneratedBy A M d) (C : M →ₗ[k] (Fin n → k))
    (hC : Function.Injective C) (a0 : Fin n)
    (rel : Fin n → Fin n → Prop) (hrefl : ∀ a, rel a a)
    (hraise : ∀ v a b, FiniteRowLeadingWeight.HasLeading (C v) a → rel a b →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) b) :
    ∃ (S : Finset M) (label : M → Fin n),
      Submodule.span A (S : Set M) = ⊤ ∧
      (∀ v ∈ S, v ≠ 0 ∧ FiniteRowLeadingWeight.HasLeading (C v) (label v)) ∧
      Set.InjOn label (S : Set M) ∧
      IsAntichain rel (S.image label : Set (Fin n)) := by
  have hex (x : M) (hx : x ≠ 0) :
      ∃ a, FiniteRowLeadingWeight.HasLeading (C x) a :=
    FiniteRowLeadingWeight.exists_leading
      (fun he => hx (hC (he.trans (map_zero C).symm)))
  let label : M → Fin n := fun x => if hx : x ≠ 0 then (hex x hx).choose else a0
  have hlead (x : M) (hx : x ≠ 0) :
      FiniteRowLeadingWeight.HasLeading (C x) (label x) := by
    simpa only [label, dif_pos hx] using (hex x hx).choose_spec
  have hcancel : ∀ x y : M, x ≠ 0 → y ≠ 0 → rel (label x) (label y) →
      (PUnit.unit : PUnit) = PUnit.unit → ∃ r : A,
        FiniteRowLeadingWeight.weight (C (y - r • x)) <
          FiniteRowLeadingWeight.weight (C y) := by
    intro x y hx hy hr _
    obtain ⟨r, hrlead⟩ := hraise x (label x) (label y) (hlead x hx) hr
    let c : k := C y (label y) / C (r • x) (label y)
    have he : c * C (r • x) (label y) = C y (label y) :=
      div_mul_cancel₀ _ hrlead.1
    have hscaled : FiniteRowLeadingWeight.HasLeading
        (c • C (r • x)) (label y) := by
      constructor
      · change c * C (r • x) (label y) ≠ 0
        rw [he]
        exact (hlead y hy).1
      · intro b hb
        change c * C (r • x) b = 0
        rw [hrlead.2 b hb, mul_zero]
    have hdrop := FiniteRowLeadingWeight.cancellation_decreases_weight
      hscaled (hlead y hy) he
    refine ⟨c • r, ?_⟩
    have hact : C ((c • r) • x) = c • C (r • x) := by
      rw [smul_assoc, map_smul]
    rw [map_sub, hact]
    exact hdrop
  obtain ⟨v, hv, hanti⟩ :=
    LeadingTermMinimalGenerators.exists_generators_orbit_antichains
      d hd (fun x => FiniteRowLeadingWeight.weight (C x)) rel label
      (fun _ => PUnit.unit) hcancel
  let t : Finset (Fin d) := Finset.univ.filter (fun i => v i ≠ 0)
  let S : Finset M := t.image v
  have hmem {x : M} (hx : x ∈ S) : ∃ i : Fin d, v i = x ∧ v i ≠ 0 := by
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    exact ⟨i, hix, (Finset.mem_filter.mp hi).2⟩
  have hspan : Submodule.span A (S : Set M) = ⊤ := by
    apply top_unique
    rw [← hv]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : v i = 0
    · rw [hi]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
  have hantiS {x y : M} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
      ¬rel (label x) (label y) := by
    obtain ⟨i, rfl, hi⟩ := hmem hx
    obtain ⟨j, rfl, hj⟩ := hmem hy
    exact hanti i j (fun he => hne (congrArg v he)) hi hj rfl
  refine ⟨S, label, hspan, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl, hi⟩ := hmem hx
    exact ⟨hi, hlead _ hi⟩
  · intro x hx y hy he
    by_contra hne
    exact hantiS hx hy hne (by rw [he]; exact hrefl _)
  · intro a ha b hb hne hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact hantiS hx hy (fun he => hne (congrArg label he)) hr

end SymmetricSubgroupAsymptotics
