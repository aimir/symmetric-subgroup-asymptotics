import SymmetricSubgroupAsymptotics.GaronziMarotiOriginalFiniteTailResidual
import SymmetricSubgroupAsymptotics.FiniteModelNestedClassTailInstaller

/-! All remaining GM branches have bounded ACTUAL original degree.
The cutoff is selected solely from fixed-menu tails before any bad group.
This is a bounded-counterexample reduction,  not the full GM theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GaronziMarotiFiniteBoundedCounterexample
open PrimitiveSocleRawStructure
open GaronziMarotiMathieuTwelveResidualReduction
open GaronziMarotiOriginalFiniteTailResidual
open GaronziMarotiFinitePrimitiveBoundedResidual (model)

noncomputable def nestedCutoff : ℕ := Classical.choose
  (FiniteModelNestedClassTailInstaller.finite_family_original_refinement_threshold model)
noncomputable def classTailCutoff : ℕ :=
  max GaronziMarotiOriginalFiniteTailResidual.classTailCutoff (9*nestedCutoff+1)

section Original
variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω] {ω₀ : Ω}
    (D : OriginalMinimalBlock (A := A) ω₀)
    (hbad : (5 ^ (Nat.card Ω - 1)) < (Nat.card (ConjClasses A) ^ 3))
    (hSmaller : ∀ (m : ℕ), (m < Nat.card Ω) → (4 ≤ m) →
      ∀ L : Subgroup (Equiv.Perm (Fin m)), Nat.card (ConjClasses L)^3 ≤ 5^(m-1))

include hbad hSmaller in
theorem nested_residual_degree_lt (h : RefinementResidual D) : Nat.card Ω < 9*nestedCutoff := by
  letI := D.top_pretransitive
  obtain ⟨E, h⟩ := h
  letI := OriginalMinimalBlockTopRefinement.action D E
  obtain ⟨hblocks, y, L, hL, hlocalbad, F, i, hi, ⟨e⟩, K, hK, hdegree, hlog, hfail⟩ := h
  have htop : 4 ≤ Nat.card D.Points := by
    have hp := E.degree_product
    have he := E.degrees_ge_two
    have hm := Nat.mul_le_mul he.1 he.2
    omega
  have hsmall : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3 := by
    by_contra h
    have hfour : 4 ≤ Nat.card D.Fibre := by have hh := D.degrees_ge_two.1; omega
    have hc := GaronziMarotiLargeBlockCubeReduction.exact_exponent_large_block_cube_step
      D.map D.map_equivariant (Nat.card D.Fibre) hfour htop D.fibre_card_at hSmaller
    exact (not_lt_of_ge hc hbad).elim
  have hinner : Nat.card E.Fibre < nestedCutoff := by
    by_contra hlarge
    obtain ⟨j, ⟨ej⟩⟩ := model_in_menu F i hi e
    have hN := @Classical.choose_spec _ _
      (FiniteModelNestedClassTailInstaller.finite_family_original_refinement_threshold model)
    have hc := hN (A := A) (Ω := Ω) D hsmall E y F j ej
      (by change nestedCutoff ≤ Nat.card E.Fibre; omega) L
    exact (not_lt_of_ge hc hlocalbad).elim
  have hp := D.degree_product
  have he := E.degree_product
  have hm : Nat.card Ω ≤ 9*Nat.card E.Fibre := by
    have h1 := Nat.mul_le_mul_right (Nat.card D.Points) (show Nat.card D.Fibre ≤ 3 by omega)
    have h2 := Nat.mul_le_mul_left (Nat.card E.Fibre) (show Nat.card E.Points ≤ 3 by omega)
    nlinarith
  omega
end Original

/-- All cutoffs are named fixed-menu constants; no desired class bound
or failed-group degree is used to define them. Minimal IH remains explicit. -/
theorem garonziMaroti_or_bounded_minimal_counterexample (hCFSG : CFSG.CFSGClassification) :
    GaronziMarotiConjugacyClassBound ∨
      ∃ n : ℕ, 4 ≤ n ∧ n < classTailCutoff ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5^(n-1) < Nat.card (ConjClasses L)^3 ∧
        (∀ m : ℕ, m  <  n → 4 ≤ m → ∀ K : Subgroup (Equiv.Perm (Fin m)),
          Nat.card (ConjClasses K)^3 ≤ 5^(m-1)) ∧ OriginalResidualWitness L (Fin n) := by
  rcases garonziMaroti_or_bounded_counterexample_or_original_nested hCFSG with h | h
  · exact Or.inl h
  · obtain ⟨n, hn, L, hbad, hSmaller, h⟩ := h
    right
    rcases h with ⟨hbound, hkeep⟩ | ⟨ht, ω, D, hD⟩
    · exact ⟨n, hn, hbound.trans_le (le_max_left _ _), L, hbad, hSmaller, hkeep⟩
    · letI := ht
      have hb : 5^(Nat.card (Fin n)-1) < Nat.card (ConjClasses L)^3 := by
        simpa only [Nat.card_fin] using hbad
      have hs : ∀ m : ℕ, m  <  Nat.card (Fin n) → 4 ≤ m →
          ∀ K : Subgroup (Equiv.Perm (Fin m)), Nat.card (ConjClasses K)^3 ≤ 5^(m-1) := by
        simpa only [Nat.card_fin] using hSmaller
      have hh := nested_residual_degree_lt D hb hs hD
      simp only [Nat.card_fin] at hh
      have hbound : n < classTailCutoff := hh.trans_le
        ((Nat.le_succ _).trans (le_max_right _ _))
      have hkeep : OriginalResidualWitness L (Fin n) :=
        Or.inr (Or.inr (Or.inr ⟨ht, ω, D, Or.inr (Or.inr hD)⟩))
      exact ⟨n, hn, hbound, L, hbad, hSmaller, hkeep⟩

end SymmetricSubgroupAsymptotics.GaronziMarotiFiniteBoundedCounterexample
