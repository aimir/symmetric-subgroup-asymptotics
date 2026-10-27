import SymmetricSubgroupAsymptotics.GaronziMarotiFinitePrimitiveBoundedResidual
import SymmetricSubgroupAsymptotics.FiniteModelOriginalClassTailInstallers

/-! The cutoff is constructed from the fixed25-model tails BEFORE choosing
any failed group. A genuine minimal counterexample supplies strict-smaller
induction. Only the original nested-refinement branch remains unbounded. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GaronziMarotiOriginalFiniteTailResidual
open PrimitiveSocleRawStructure
open GaronziMarotiMathieuTwelveResidualReduction
open GaronziMarotiFinitePrimitiveBoundedResidual (Menu model menuIndex)

noncomputable def primitiveCutoff : ℕ := Classical.choose
  GaronziMarotiFinitePrimitiveBoundedResidual.exists_remaining_threshold
noncomputable def componentCutoff : ℕ := max 4 (Classical.choose
  (FiniteModelPrimitiveClassReserveTail.finite_family_threshold model 2))
noncomputable def topCutoff : ℕ := Classical.choose
  (FiniteModelOriginalClassTailInstallers.finite_family_small_fibre_threshold model)
noncomputable def commonCutoff : ℕ := max primitiveCutoff (max componentCutoff topCutoff)
noncomputable def classTailCutoff : ℕ := max 36856 (3*commonCutoff+1)

theorem model_in_menu {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (i : CFSG.Index) (hi : RemainingFiniteSimpleType i)
    (e : D.Simple ≃* i.Model) : ∃ j : Menu, Nonempty (D.Simple ≃* model j) := by
  cases i <;> try { exact hi.1.elim }
  case tits => exact ⟨⟨none, by simp⟩, ⟨e⟩⟩
  case sporadic s =>
    have hs11 : some s≠some CFSG.Sporadic.m11 := by
      intro h; exact hi.2.1 (congrArg CFSG.Index.sporadic (Option.some.inj h))
    have hs12 : some s≠some CFSG.Sporadic.m12 := by
      intro h; exact hi.2.2 (congrArg CFSG.Index.sporadic (Option.some.inj h))
    exact ⟨⟨some s, hs11, hs12⟩, ⟨e⟩⟩

section Original
variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω] {ω₀ : Ω}
    (D : OriginalMinimalBlock (A := A) ω₀)
    (hbad : (5 ^ (Nat.card Ω - 1)) < (Nat.card (ConjClasses A) ^ 3))
    (hSmaller : ∀ (m : ℕ), (m < Nat.card Ω) → (4 ≤ m) →
      ∀ L : Subgroup (Equiv.Perm (Fin m)), Nat.card (ConjClasses L)^3 ≤ 5^(m-1))

include hbad hSmaller in
theorem component_residual_degree_lt (h : ComponentResidual D) :
    Nat.card Ω < 3*componentCutoff := by
  obtain ⟨hblocks, x, L, hL, E, i, hi, ⟨e⟩, K, hK, hdegree, hlog, hfail⟩ := h
  have hsmall : Nat.card D.Fibre < componentCutoff := by
    by_contra hlarge
    have hlarge' : componentCutoff ≤ Nat.card D.Fibre := by omega
    have hfour : 4 ≤ Nat.card D.Fibre := (le_max_left _ _).trans hlarge'
    obtain ⟨j, ⟨ej⟩⟩ := model_in_menu E i hi e
    have hN := Classical.choose_spec (FiniteModelPrimitiveClassReserveTail.finite_family_threshold model 2)
    have hg : ∀ V : Subgroup (originalBlockComponent D.map D.map_equivariant x),
        V.IsSubnormal → V≠⊤ → Nat.card (ConjClasses V)^3 ≤ 5^(Nat.card D.Fibre-2) := by
      intro V _ _
      have hh := hN j E ej
        (by rw [D.fibre_card_at x]; exact (le_max_right _ _).trans hlarge') V
      simpa only [D.fibre_card_at x] using hh
    have hc := SmallTopProperSubnormalClassGapBound.class_cube_le_of_proper_subnormal_gaps
      D.map D.map_equivariant x (Nat.card D.Fibre) hfour (D.fibre_card_at x) hblocks hg hSmaller
    exact (not_lt_of_ge hc hbad).elim
  have hp := D.degree_product
  have hm : Nat.card Ω ≤ 3*Nat.card D.Fibre := by
    have hh := Nat.mul_le_mul_left (Nat.card D.Fibre) (show Nat.card D.Points ≤ 3 by omega)
    omega
  omega

include hbad hSmaller in
theorem top_residual_degree_lt (h : TopResidual D) : Nat.card Ω < 3*topCutoff := by
  obtain ⟨E, i, hi, ⟨e⟩, K, hK, hdegree, hlog, hfail⟩ := h
  have htop : 4 ≤ Nat.card D.Points := by
    obtain ⟨ell, hell⟩ := exists_leastProperIndex E.Simple
    have hfive := nonabelianSimple_leastProperIndex_five_le
      (fun hc => E.noncommutative (isMulCommutative_iff.mpr hc)) hell.1
    have hh := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree E ell hell
    omega
  have hfibre : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3 := by
    by_contra h
    have hfour : 4 ≤ Nat.card D.Fibre := by have hh := D.degrees_ge_two.1; omega
    have hc := GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
      D.map D.map_equivariant (Nat.card D.Fibre) hfour htop D.fibre_card_at hSmaller
    exact (not_lt_of_ge hc hbad).elim
  have hsmall : Nat.card D.Points < topCutoff := by
    by_contra hlarge
    obtain ⟨j, ⟨ej⟩⟩ := model_in_menu E i hi e
    have hN := @Classical.choose_spec _ _
      (FiniteModelOriginalClassTailInstallers.finite_family_small_fibre_threshold model)
    have hh := hN (A := A) (Ω := Ω) (X := D.Points)
      D.map D.map_equivariant (Nat.card D.Fibre) hfibre D.fibre_card_at
      E j ej (by change topCutoff ≤ Nat.card D.Points; omega) (⊤ : Subgroup A)
    have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A)
    rw [he] at hh
    have hc := hh.trans (Nat.pow_le_pow_right (by decide : 0 < 5) (by omega : Nat.card Ω-2 ≤ Nat.card Ω-1))
    exact (not_lt_of_ge hc hbad).elim
  have hp := D.degree_product
  have hm : Nat.card Ω ≤ 3*Nat.card D.Points := by
    have hh := Nat.mul_le_mul_right (Nat.card D.Points) (show Nat.card D.Fibre ≤ 3 by omega)
    omega
  omega
end Original

variable (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]

def NestedResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive G X,
    letI := ht
    ∃ ω₀ : X, ∃ D : OriginalMinimalBlock (A := G) ω₀, RefinementResidual D

def OriginalResidualWitness : Prop :=
  ActualSmallFibreResidual G X ∨ ActualBoundedNonaffineResidual G X ∨
    GaronziMarotiMathieuTwelveResidualReduction.ActualFiniteModelResidual G X

private theorem common_lt_cutoff : 3*commonCutoff < classTailCutoff :=
  lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

private theorem refine_minimal_residual (n : ℕ) (hn : 4 ≤ n)
    (L : Subgroup (Equiv.Perm (Fin n)))
    (hbad : 5^(n-1) <  Nat.card (ConjClasses L)^3)
    (hSmaller : ∀ m : ℕ, m  <  n → 4 ≤ m →
      ∀ K : Subgroup (Equiv.Perm (Fin m)), Nat.card (ConjClasses K)^3 ≤ 5^(m-1))
    (hres : ActualSmallFibreResidual L (Fin n) ∨ ActualBoundedNonaffineResidual L (Fin n) ∨
      GaronziMarotiMathieuTwelveResidualReduction.ActualFiniteModelResidual L (Fin n)) :
    (n < classTailCutoff ∧ OriginalResidualWitness L (Fin n)) ∨ NestedResidual L (Fin n) := by
  have hkeep : OriginalResidualWitness L (Fin n) := hres
  have hs : ∀ m : ℕ, m  <  Nat.card (Fin n) → 4 ≤ m →
      ∀ K : Subgroup (Equiv.Perm (Fin m)), Nat.card (ConjClasses K)^3 ≤ 5^(m-1) := by
    simpa only [Nat.card_fin] using hSmaller
  have hb : 5^(Nat.card (Fin n)-1) <  Nat.card (ConjClasses L)^3 := by
    simpa only [Nat.card_fin] using hbad
  have h36856 : 36856 ≤ classTailCutoff := le_max_left _ _
  rcases hres with h | h | h
  · obtain ⟨ht, ω, D, hshape, hrest⟩ := h
    have hh := hshape.2
    simp only [Nat.card_fin] at hh
    exact Or.inl ⟨by omega, hkeep⟩
  · obtain ⟨ht, ω, D, hshape, hrest⟩ := h
    letI := ht
    have hh := OriginalMinimalBlockNonaffineShapeResidual.bounded_degree_of_nonaffine_component D hshape
    simp only [Nat.card_fin] at hh
    exact Or.inl ⟨by omega, hkeep⟩
  · rcases h with h | ⟨ht, ω, D, h⟩
    · obtain ⟨hp, E, i, ⟨e⟩, hi, hform⟩ := h
      have hsmall : n < primitiveCutoff := by
        by_contra hlarge
        have hN := @Classical.choose_spec _ _
          GaronziMarotiFinitePrimitiveBoundedResidual.exists_remaining_threshold
        have hh := hN (G := L) (X := Fin n) E i hi e
          (by simpa only [Nat.card_fin] using (show primitiveCutoff ≤ n by omega))
          (⊤ : Subgroup L)
        have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L)
        rw [he] at hh
        simp only [Nat.card_fin] at hh
        exact (not_lt_of_ge hh hbad).elim
      have hc : primitiveCutoff ≤ commonCutoff := le_max_left _ _
      have hg := common_lt_cutoff
      exact Or.inl ⟨by omega, hkeep⟩
    · letI := ht
      rcases h with h | h | h
      · have hh := component_residual_degree_lt D hb hs h
        simp only [Nat.card_fin] at hh
        have hc : componentCutoff ≤ commonCutoff :=
          (le_max_left _ _).trans (le_max_right _ _)
        have hg := common_lt_cutoff
        exact Or.inl ⟨by omega, hkeep⟩
      · have hh := top_residual_degree_lt D hb hs h
        simp only [Nat.card_fin] at hh
        have hc : topCutoff ≤ commonCutoff :=
          (le_max_right _ _).trans (le_max_right _ _)
        have hg := common_lt_cutoff
        exact Or.inl ⟨by omega, hkeep⟩
      · exact Or.inr ⟨ht, ω, D, h⟩

/-- The named cutoff depends only on the fixed-menu tails. Minimality
constructs hSmaller internally; it is not a desired GM callback. -/
theorem garonziMaroti_or_bounded_counterexample_or_original_nested
    (hCFSG : CFSG.CFSGClassification) :
    GaronziMarotiConjugacyClassBound ∨
      ∃ n : ℕ, 4 ≤ n ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5^(n-1) <  Nat.card (ConjClasses L)^3 ∧
        (∀ m : ℕ, m  <  n → 4 ≤ m → ∀ K : Subgroup (Equiv.Perm (Fin m)),
          Nat.card (ConjClasses K)^3 ≤ 5^(m-1)) ∧
        ((n < classTailCutoff ∧ OriginalResidualWitness L (Fin n)) ∨ NestedResidual L (Fin n)) := by
  by_cases hcube : ∀ n : ℕ, 4 ≤ n → ∀ L : Subgroup (Equiv.Perm (Fin n)),
      Nat.card (ConjClasses L)^3 ≤ 5^(n-1)
  · left
    intro n hn L
    exact (GaronziMarotiTransitiveTarget.cube_le_iff_real_bound _ n (by omega)).mp (hcube n hn L)
  · push_neg at hcube
    obtain ⟨n, hn, L, hbad⟩ := hcube
    obtain ⟨m, _, hm, H, hH, hSmaller⟩ :=
      GaronziMarotiGlobalBoundedCounterexample.exists_minimal_counterexample n hn L hbad
    have hres := GaronziMarotiMathieuTwelveResidualReduction.minimal_counterexample_has_actual_residual
      hCFSG m hm H hH hSmaller
    exact Or.inr ⟨m, hm, H, hH, hSmaller, refine_minimal_residual m hm H hH hSmaller hres⟩

end SymmetricSubgroupAsymptotics.GaronziMarotiOriginalFiniteTailResidual
