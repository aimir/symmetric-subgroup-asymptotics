import SymmetricSubgroupAsymptotics.CyclicQuotientOddHall
import SymmetricSubgroupAsymptotics.RepresentationGeneratorHead
import SymmetricSubgroupAsymptotics.TraceyBinaryFormulaInput
import SymmetricSubgroupAsymptotics.TraceyPrimePowerInput
import Mathlib.GroupTheory.Solvable

/-!
# Tracey's soluble-orbit induced-module formula

This file records the exact published input used at the degree-four affine
seam.  The source is Tracey, *Minimal generation of transitive permutation
groups*, J. Algebra 509 (2018), Theorem 4.24(ii)(b) and Corollary
4.25(ii)(b), printed pages 27--30.

We use the literal specialization `H_1 = H`, over `F_2`.  Thus Tracey's
local parameters are `d = 1` and `a = dim V`, and the coefficient in
Corollary 4.25 is

`min (dim V) (chi(P'_N ∩ core_G(H), V*)))`.

For every orbit of the displayed soluble subgroup `N` on `G/H`, the
integer `E_sol(s_i,2)` is retained through both defining inequalities:

* `E_sol(s_i,2) <= (s_i)_2`;
* `2^K E_sol(s_i,2) <= s_i * choose(K,floor(K/2))`,
  where `K = sum r(q-1)` over the prime powers in `s_i`.

The input below states exactly this formula.  It does not assume the
half-degree consequence, the existence of the soluble subgroup, the Hall
subgroup, or the fact that the local dual orbit count is one.  Those are
separate project proofs at the actual retained group.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

/-- The exact two integer inequalities defining the binary
`E_sol(s,2)` entry in Tracey's Definition 1.5. -/
def TraceyBinarySolubleFormulaBounds (s d : ℕ) : Prop :=
  d ≤ ordProj[2] s ∧
    2 ^ traceyBinaryK s * d ≤
      s * (traceyBinaryK s).choose (traceyBinaryK s / 2)

theorem TraceyBinarySolubleFormulaBounds.toFormulaBounds
    {s d : ℕ} (h : TraceyBinarySolubleFormulaBounds s d) :
    TraceyBinaryFormulaBounds s d :=
  Or.inl h

/-- Every nontrivial orbit pays at most half its size.  This is the
arithmetic consequence of the exact `E_sol` inequalities; it is not part
of the literature assumption. -/
theorem traceyBinarySolubleFormulaBounds_two_le
    {s d : ℕ} (hs : 2 ≤ s)
    (h : TraceyBinarySolubleFormulaBounds s d) :
    2 * d ≤ s := by
  by_cases ho1 : ordCompl[2] s = 1
  · let a := s.factorization 2
    have hsEq : s = 2 ^ a := by
      have hdecomp := Nat.ordProj_mul_ordCompl_eq_self s 2
      simpa [a, ho1] using hdecomp.symm
    have ha1 : 1 ≤ a := by
      by_contra ha
      have ha0 : a = 0 := by omega
      norm_num [hsEq, ha0] at hs
    have hK : traceyBinaryK s = a := by
      rw [hsEq, traceyBinaryK_two_pow]
    have hd : d ≤ a.choose (a / 2) := by
      have hmain := h.2
      rw [hK, hsEq] at hmain
      exact Nat.le_of_mul_le_mul_left hmain (pow_pos (by decide) a)
    exact (Nat.mul_le_mul_left 2 hd).trans (by
      simpa [hsEq] using binary_middle_twice_le_power a ha1)
  · have hs2 : s ≠ 2 := by
      intro hsEq
      subst s
      have ho2 : ordCompl[2] 2 = 1 := by
        rw [show (2 : ℕ) = 2 ^ 1 by norm_num]
        exact Nat.ordCompl_self_pow Nat.prime_two
      exact ho1 ho2
    have hs4 : s ≠ 4 := by
      intro hsEq
      subst s
      have ho4 : ordCompl[2] 4 = 1 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.ordCompl_self_pow Nat.prime_two
      exact ho1 ho4
    have hs3 : 3 ≤ s := by omega
    have hthree :=
      traceyBinaryFormulaBounds_three_eighths_of_three_le_of_ne_four
        hs3 hs4 h.toFormulaBounds
    omega

/-- The subgroup of the point stabilizer corresponding to
`P'_N ∩ core_G(H)` in Tracey's coefficient. -/
def traceyPrimeToCoreSubgroup
    {G I : Type} [Group G] [MulAction G I]
    (i : I) (N : Subgroup G) (P : Subgroup N) :
    Subgroup (MulAction.stabilizer G i) :=
  ((P.map N.subtype) ⊓ (MulAction.stabilizer G i).normalCore).comap
    (MulAction.stabilizer G i).subtype

/-- Orbit equivalence on the nonzero vectors of one representation.  Its
quotient cardinal is Tracey's `chi(L,V*)`.  We define the relation directly
from the representation so that no ambient action instance is hidden. -/
def representationNonzeroOrbitRel
    {k L V : Type} [Field k] [Group L]
    [AddCommGroup V] [Module k V]
    (rho : Representation k L V) :
    Setoid {v : V // v ≠ 0} where
  r x y := ∃ g : L, rho g x.1 = y.1
  iseqv := {
    refl := fun x ↦ ⟨1, by simp⟩
    symm := by
      rintro x y ⟨g, hg⟩
      refine ⟨g⁻¹, ?_⟩
      calc
        rho g⁻¹ y.1 = rho g⁻¹ (rho g x.1) := congrArg (rho g⁻¹) hg.symm
        _ = x.1 := by
          change (rho g⁻¹ * rho g) x.1 = x.1
          rw [← map_mul, inv_mul_cancel, map_one]
          rfl
    trans := by
      rintro x y z ⟨g, hg⟩ ⟨h, hh⟩
      refine ⟨h * g, ?_⟩
      calc
        rho (h * g) x.1 = rho h (rho g x.1) := by
          rw [map_mul]
          rfl
        _ = rho h y.1 := congrArg (rho h) hg
        _ = z.1 := hh }

/-- Tracey's literal `chi(P'_N ∩ core_G(H), V*)` in the point-stabilizer
specialization. -/
def traceyLocalDualOrbitCount
    {G I V : Type} [Group G] [MulAction G I]
    [AddCommGroup V] [Module (ZMod 2) V]
    (i : I)
    (rho : Representation (ZMod 2) (MulAction.stabilizer G i) V)
    (N : Subgroup G) (P : Subgroup N) : ℕ :=
  Nat.card (Quotient (representationNonzeroOrbitRel
    (rho.dual.comp (traceyPrimeToCoreSubgroup i N P).subtype)))

/-- Tracey, Theorem 4.24(ii)(b) and Corollary 4.25(ii)(b), with
`H_1 = H` and field `F_2`.  The soluble subgroup, its actual
`2`-complement, all orbit sizes and both defining `E_sol` inequalities are
visible in the statement. -/
def TraceySolubleOrbitInducedModuleInput : Prop :=
  ∀ (G I : Type) [Group G] [Finite G] [Finite I]
    [MulAction G I] [MulAction.IsPretransitive G I]
    (i : I)
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
      [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) (MulAction.stabilizer G i) V)
    (N : Subgroup G) [IsSolvable N]
    (P : Subgroup N), IsTwoComplement P →
    ∀ M : Subrepresentation
      (Representation.ind (MulAction.stabilizer G i).subtype rho),
      ∃ e : MulAction.orbitRel.Quotient N I → ℕ,
        (∀ o : MulAction.orbitRel.Quotient N I,
          TraceyBinarySolubleFormulaBounds (Nat.card o.orbit) (e o)) ∧
        RepresentationGeneratedBy M.toRepresentation
          (min (Module.finrank (ZMod 2) V)
              (traceyLocalDualOrbitCount i rho N P) *
            ∑ o : MulAction.orbitRel.Quotient N I, e o)

end SymmetricSubgroupAsymptotics

end
