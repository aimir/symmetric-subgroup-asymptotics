import SymmetricSubgroupAsymptotics.SimpleCyclicQuotientDimension
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.GroupTheory.GroupAction.Basic

/-! A transitive action on the actual basis lines makes a monomial
representation cyclic, including arbitrary nonzero scalar signs. The
simple-group quotient dichotomy consequently applies to its literal
invariant subspaces, without a semisimplicity or unsigned-action premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TransitiveMonomialCyclicSpan

variable {K S I V : Type} [Field K] [Group S] [MulAction S I]
    [MulAction.IsPretransitive S I] [AddCommGroup V] [Module K V]

/-- Unit multiples of a transitive basis orbit span the original module. -/
theorem span_orbit_eq_top (rho : Representation K S V) (b : Module.Basis I K V)
    (hmonomial : ∀ (g : S) (i : I), ∃ a : Kˣ, rho g (b i) = (a : K) • b (g • i))
    (i0 : I) :
    Submodule.span K (Set.range (fun g : S => rho g (b i0))) = ⊤ := by
  classical
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S i0 i
  obtain ⟨a, ha⟩ := hmonomial g i0
  have hmem : rho g (b i0) ∈
      Submodule.span K (Set.range (fun h : S => rho h (b i0))) :=
    Submodule.subset_span ⟨g, rfl⟩
  rw [ha, hg] at hmem
  have hinv := (Submodule.span K (Set.range (fun h : S => rho h (b i0)))).smul_mem
    ((a⁻¹ : Kˣ) : K) hmem
  simpa [smul_smul] using hinv

/-- The quotient is at most one dimensional, or its actual general
linear group has order divisible by the finite simple source order. -/
theorem quotient_dichotomy [Finite S] [IsSimpleGroup S] [FiniteDimensional K V]
    (rho : Representation K S V) (b : Module.Basis I K V)
    (hmonomial : ∀ (g : S) (i : I), ∃ a : Kˣ, rho g (b i) = (a : K) • b (g • i))
    (i0 : I) (N : Submodule K V) (hstable : ∀ g : S, N ≤ N.comap (rho g)) :
    Module.finrank K (V ⧸ N) ≤ 1 ∨
      Nat.card S ∣ Nat.card (Matrix.GeneralLinearGroup (Fin (Module.finrank K (V ⧸ N))) K) :=
  SimpleCyclicQuotientDimension.cyclic_quotient_dichotomy rho (b i0)
    (span_orbit_eq_top rho b hmonomial i0) N hstable

/-- The same conclusion retains the codimension of the same subspace. -/
theorem codimension_dichotomy [Finite S] [IsSimpleGroup S] [FiniteDimensional K V]
    (rho : Representation K S V) (b : Module.Basis I K V)
    (hmonomial : ∀ (g : S) (i : I), ∃ a : Kˣ, rho g (b i) = (a : K) • b (g • i))
    (i0 : I) (N : Submodule K V) (hstable : ∀ g : S, N ≤ N.comap (rho g)) :
    Module.finrank K V - Module.finrank K N ≤ 1 ∨
      Nat.card S ∣ Nat.card (Matrix.GeneralLinearGroup
        (Fin (Module.finrank K V - Module.finrank K N)) K) :=
  SimpleCyclicQuotientDimension.codimension_dichotomy rho (b i0)
    (span_orbit_eq_top rho b hmonomial i0) N hstable

end SymmetricSubgroupAsymptotics.TransitiveMonomialCyclicSpan
