import SymmetricSubgroupAsymptotics.PermutationOrbitHeadSection

/-!
# Visible binary transitive-module input

This file records the exact coarse consequence of Tracey's induced-module
theorem used by the coupled-socle orbit filtration.  It remains an explicit
hypothesis: deriving it from the published `E` and `E_sol` formulae, including
their small-degree arithmetic, is a separate formal obligation.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The common integer cap needed on a transitive binary orbit.  Singleton
orbits retain their one-dimensional head; from degree eight onward the
three-eighths consequence is used. -/
def traceyBinaryOrbitCap (u : ℕ) : ℕ :=
  if u = 1 then 1 else if 8 ≤ u then 3 * u / 8 else u / 2

/-- Visible published-input interface for the binary permutation-module
head.  No axiom is declared; every consumer carries this proposition as a
hypothesis until the exact `E`/`E_sol` derivation is installed. -/
def TraceyBinaryOrbitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G]
    (X : Type) [Finite X] [MulAction G X] [MulAction.IsPretransitive G X]
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G X)),
    Module.finrank (ZMod 2) (M.toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) G (ZMod 2))) ≤
      traceyBinaryOrbitCap (Nat.card X)

theorem traceyBinaryOrbitCap_twice_le (u : ℕ) (hu : 2 ≤ u) :
    2 * traceyBinaryOrbitCap u ≤ u := by
  rw [traceyBinaryOrbitCap, if_neg (by omega)]
  split_ifs
  · have h := Nat.div_mul_le_self (3 * u) 8
    omega
  · have h := Nat.div_mul_le_self u 2
    omega

theorem traceyBinaryOrbitCap_eight_le_three_mul
    (u : ℕ) (hu : 8 ≤ u) :
    8 * traceyBinaryOrbitCap u ≤ 3 * u := by
  rw [traceyBinaryOrbitCap, if_neg (by omega), if_pos hu]
  simpa only [Nat.mul_comm] using Nat.div_mul_le_self (3 * u) 8

/-- Apply the visible input to one literal orbit of an arbitrary action. -/
theorem traceyBinaryOrbit_head_le
    (hTracey : TraceyBinaryOrbitInput)
    (G : Type) [Group G] [Finite G]
    (X : Type) [Finite X] [MulAction G X]
    (o : MulAction.orbitRel.Quotient G X)
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G o.orbit)) :
    Module.finrank (ZMod 2) (M.toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) G (ZMod 2))) ≤
      traceyBinaryOrbitCap (Nat.card o.orbit) := by
  letI : MulAction.IsPretransitive G o.orbit := ⟨by
    intro x y
    exact MulAction.exists_smul_eq G x y⟩
  exact hTracey G o.orbit M

end SymmetricSubgroupAsymptotics

end
