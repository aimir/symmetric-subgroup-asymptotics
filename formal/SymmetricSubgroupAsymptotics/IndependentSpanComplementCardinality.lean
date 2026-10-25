import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega

/-! Exact free-image capacities from actual independent frames. These
counts apply fibrewise to sparse automorphism charts; they do not replace
independence by an ambient unconstrained column count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.IndependentSpanComplementCardinality

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite V]

theorem card_span {k : ℕ} (s : Fin k → V) (hs : LinearIndependent K s) :
    Nat.card (Submodule.span K (Set.range s)) = Nat.card K ^ k := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  have hd : Module.finrank K (Submodule.span K (Set.range s)) = k := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hs
  rw [Module.natCard_eq_pow_finrank (K := K) (V := Submodule.span K (Set.range s)), hd]

theorem card_complement_span {k : ℕ} (s : Fin k → V) (hs : LinearIndependent K s) :
    Nat.card {v : V // v ∉ Submodule.span K (Set.range s)} =
      Nat.card V - Nat.card K ^ k := by
  have hsum : Nat.card (Submodule.span K (Set.range s)) +
      Nat.card {v : V // v ∉ Submodule.span K (Set.range s)} = Nat.card V := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun v : V => v ∈ Submodule.span K (Set.range s)))
  rw [card_span s hs] at hsum
  omega

theorem card_sigma_complement_span {U : Type*} [Finite U] {k : ℕ}
    (s : U → Fin k → V) (hs : ∀ u : U, LinearIndependent K (s u)) :
    Nat.card ((u : U) × {v : V // v ∉ Submodule.span K (Set.range (s u))}) =
      Nat.card U * (Nat.card V - Nat.card K ^ k) := by
  letI : Fintype U := Fintype.ofFinite _
  have hc (u : U) := card_complement_span (s u) (hs u)
  rw [Nat.card_sigma]
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Nat.cast_id]

end SymmetricSubgroupAsymptotics.IndependentSpanComplementCardinality
