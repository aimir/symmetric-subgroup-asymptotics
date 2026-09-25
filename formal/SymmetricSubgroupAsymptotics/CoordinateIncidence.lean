import SymmetricSubgroupAsymptotics.ComplementCount

/-!
# Simultaneous coordinate relations and finite fibre bounds

A basis chosen from the coordinate restrictions provides pivot coordinates.
Fixing the other coordinates fixes every pivot outcome. The argument retains
the whole relation space and does not assume independent random outcomes.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

section Pivots

variable {F E ι : Type*} [Field F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E] [Fintype ι]

/-- A basis of the relation dual consisting of actual coordinate
restrictions. The coordinates are distinct, without imposing an order. -/
structure CoordinatePivotSystem (c : ι → Module.Dual F E) where
  indices : Set ι
  basis : Module.Basis indices F (Module.Dual F E)
  basis_eq : ∀ i, basis i = c i.1

omit [FiniteDimensional F E] [Fintype ι] in
/-- Any spanning family of coordinate restrictions admits a pivot system. -/
theorem coordinatePivotSystem_nonempty (c : ι → Module.Dual F E)
    (hc : Submodule.span F (Set.range c) = ⊤) :
    Nonempty (CoordinatePivotSystem c) := by
  obtain ⟨κ, a, ha, hs, hi⟩ := exists_linearIndependent' F c
  let b : Module.Basis κ F (Module.Dual F E) :=
    Module.Basis.mk hi (by rw [hs, hc])
  let e := Equiv.ofInjective a ha
  refine ⟨⟨Set.range a, b.reindex e, ?_⟩⟩
  intro i
  rw [Module.Basis.reindex_apply]
  simp only [b, Module.Basis.mk_apply]
  change c (a (e.symm i)) = c i.1
  exact congrArg c (congrArg Subtype.val (e.apply_symm_apply i))

/-- Choose one proved pivot system; no echelon-form algorithm is required. -/
def coordinatePivotSystem (c : ι → Module.Dual F E)
    (hc : Submodule.span F (Set.range c) = ⊤) : CoordinatePivotSystem c :=
  Classical.choice (coordinatePivotSystem_nonempty c hc)

omit [FiniteDimensional F E] in
theorem CoordinatePivotSystem.card_indices {c : ι → Module.Dual F E}
    (P : CoordinatePivotSystem c) : Fintype.card P.indices = Module.finrank F E := by
  rw [← Module.finrank_eq_card_basis P.basis, Subspace.dual_finrank_eq]

/-- A relation isolating one pivot coordinate from every other pivot. -/
def CoordinatePivotSystem.isolatingVector {c : ι → Module.Dual F E}
    (P : CoordinatePivotSystem c) (i : P.indices) : E :=
  (Module.evalEquiv F E).symm (P.basis.dualBasis i)

theorem CoordinatePivotSystem.isolatingVector_apply {c : ι → Module.Dual F E}
    (P : CoordinatePivotSystem c) (i j : P.indices) :
    c j.1 (P.isolatingVector i) = if i = j then 1 else 0 := by
  rw [← P.basis_eq j]
  simpa only [eq_comm] using
    (Module.apply_evalEquiv_symm_apply F E (P.basis j) (P.basis.dualBasis i)).trans
      (P.basis.dualBasis_apply_self i j)

end Pivots

section Incidence

variable {F E ι X : Type*} [Field F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E] [Fintype ι] [AddCommGroup X] [Module F X]
  {A : ι → Type*}

/-- Actual tuples satisfying every retained linear relation between their
coordinate outcomes. The outcome maps need not themselves be linear. -/
abbrev CoordinateRelationSolutions (c : ι → Module.Dual F E) (q : ∀ i, A i → X) :=
  {f : ∀ i, A i // ∀ b : E, ∑ i, c i b • q i (f i) = 0}

/-- Fixing all nonpivot choices fixes every pivot outcome. This uses the
joint equations, not separate bounds on individual relations. -/
theorem CoordinatePivotSystem.outcomes_equal {c : ι → Module.Dual F E}
    (P : CoordinatePivotSystem c) (q : ∀ i, A i → X)
    (f g : CoordinateRelationSolutions c q)
    (hfg : ∀ i : {i : ι // i ∉ P.indices}, f.1 i.1 = g.1 i.1) (i : P.indices) :
    q i.1 (f.1 i.1) = q i.1 (g.1 i.1) := by
  have hf := f.2 (P.isolatingVector i)
  have hg := g.2 (P.isolatingVector i)
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j ↦ j ∈ P.indices)] at hf hg
  simp only [P.isolatingVector_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at hf hg
  have hn : (∑ j : {i : ι // i ∉ P.indices}, c j.1 (P.isolatingVector i) • q j.1 (f.1 j.1)) =
      ∑ j : {i : ι // i ∉ P.indices}, c j.1 (P.isolatingVector i) • q j.1 (g.1 j.1) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hfg j]
  rw [hn] at hf
  exact add_right_cancel (hf.trans hg.symm)

/-- A finite fibre bound for simultaneous coordinate relations. Every pivot
has the bounded outcome fibre; every other coordinate is counted literally. -/
theorem CoordinatePivotSystem.solution_count_le {c : ι → Module.Dual F E}
    (P : CoordinatePivotSystem c) [∀ i, Fintype (A i)]
    (q : ∀ i, A i → X) (M : ℕ)
    (hM : ∀ i x, Nat.card {a : A i // q i a = x} ≤ M) :
    Nat.card (CoordinateRelationSolutions c q) ≤
      (∏ i : {i : ι // i ∉ P.indices}, Nat.card (A i.1)) * M ^ Module.finrank F E := by
  let p : CoordinateRelationSolutions c q → ∀ i : {i : ι // i ∉ P.indices}, A i.1 :=
    fun f i ↦ f.1 i.1
  have hcount (z : ∀ i : {i : ι // i ∉ P.indices}, A i.1) :
      Nat.card {f : CoordinateRelationSolutions c q // p f = z} ≤
        M ^ Module.finrank F E := by
    by_cases hn : Nonempty {f : CoordinateRelationSolutions c q // p f = z}
    · let f₀ := Classical.choice hn
      let encode : {f : CoordinateRelationSolutions c q // p f = z} →
          ∀ i : P.indices, {a : A i.1 // q i.1 a = q i.1 (f₀.1.1 i.1)} :=
        fun f i ↦ ⟨f.1.1 i.1, P.outcomes_equal q f.1 f₀.1
          (fun j ↦ congrFun (f.2.trans f₀.2.symm) j) i⟩
      have hinj : Function.Injective encode := by
        intro f g he
        apply Subtype.ext
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ P.indices
        · exact congrArg Subtype.val (congrFun he ⟨i, hi⟩)
        · exact congrFun (f.2.trans g.2.symm) ⟨i, hi⟩
      calc
        _ ≤ Nat.card (∀ i : P.indices,
            {a : A i.1 // q i.1 a = q i.1 (f₀.1.1 i.1)}) :=
          Nat.card_le_card_of_injective encode hinj
        _ = ∏ i : P.indices,
            Nat.card {a : A i.1 // q i.1 a = q i.1 (f₀.1.1 i.1)} := Nat.card_pi
        _ ≤ ∏ _i : P.indices, M := Finset.prod_le_prod' (fun i _ ↦ hM i.1 _)
        _ = _ := by simp [P.card_indices]
    · haveI : IsEmpty {f : CoordinateRelationSolutions c q // p f = z} :=
        not_nonempty_iff.mp hn
      simp
  calc
    _ = ∑ z, Nat.card {f : CoordinateRelationSolutions c q // p f = z} := by
      rw [← Nat.card_sigma]
      exact (Nat.card_congr (Equiv.sigmaFiberEquiv p)).symm
    _ ≤ ∑ _z : (∀ i : {i : ι // i ∉ P.indices}, A i.1), M ^ Module.finrank F E :=
      Finset.sum_le_sum (fun z _ ↦ hcount z)
    _ = _ := by simp [← Nat.card_eq_fintype_card, Nat.card_pi]

end Incidence

end SymmetricSubgroupAsymptotics
