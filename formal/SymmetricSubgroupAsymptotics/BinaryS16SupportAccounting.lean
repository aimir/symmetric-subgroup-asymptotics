import SymmetricSubgroupAsymptotics.BinaryS16ResidualPartition

/-!
# Literal support accounting in the retained S16 background

The canonical seven-colour profile already separates the four critical
colours from the three positive retained-background colours.  This file puts
the corresponding half-point costs on those colours.  For every positive
realization the doubled cost is exactly the size of its literal original
orbit.  Summing over all literal orbits therefore charges support directly to
the original `Fin (2*N)` point set.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryS16SupportAccounting

open SymmetricSubgroupAsymptotics
open BinaryS16CanonicalCarrierProfile
open BinaryS16ResidualPartition

/-- Half-point support of one canonical S16 colour.  Critical colours stay in
the critical parameter and consume no retained support. -/
def halfSupport : OrbitColor → ℕ
  | .c2 | .v4 | .d8 | .e8 => 0
  | .cyclicFour => 2
  | .carrier8 => 4
  | .carrier16 => 8

theorem isPositive_iff_halfSupport_pos (c : OrbitColor) :
    c.IsPositive ↔ 0 < halfSupport c := by
  cases c <;> simp [OrbitColor.IsPositive,halfSupport]

variable {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))

/-- A positive realization consumes exactly its literal orbit size. -/
theorem doubled_halfSupport_eq_orbit_card_of_realizes
    {o : Orbit H} {c : OrbitColor}
    (hc : Realizes H o c) (hpositive : c.IsPositive) :
    2 * halfSupport c = Nat.card o.orbit := by
  cases hc with
  | c2 e he => simp [OrbitColor.IsPositive] at hpositive
  | v4 e he => simp [OrbitColor.IsPositive] at hpositive
  | d8 e he => simp [OrbitColor.IsPositive] at hpositive
  | e8 e he => simp [OrbitColor.IsPositive] at hpositive
  | cyclicFour W hpoint S hs =>
      have hmk : Nat.card
          (MulAction.orbitRel.Quotient.orbit
            (Quotient.mk'' W.point : Orbit H)) = 4 := by
        simpa only [MulAction.orbitRel.Quotient.orbit_mk] using W.orbit_card
      have heq := congrArg (fun q : Orbit H ↦ Nat.card q.orbit) hpoint
      have ho : Nat.card o.orbit = 4 := heq.symm.trans hmk
      simpa [halfSupport] using ho.symm
  | carrier8 W hpoint S hs =>
      have hmk : Nat.card
          (MulAction.orbitRel.Quotient.orbit
            (Quotient.mk'' W.point : Orbit H)) = 8 := by
        simpa only [MulAction.orbitRel.Quotient.orbit_mk] using W.orbit_card
      have heq := congrArg (fun q : Orbit H ↦ Nat.card q.orbit) hpoint
      have ho : Nat.card o.orbit = 8 := heq.symm.trans hmk
      simpa [halfSupport] using ho.symm
  | carrier16 W hpoint S hs =>
      have hmk : Nat.card
          (MulAction.orbitRel.Quotient.orbit
            (Quotient.mk'' W.point : Orbit H)) = 16 := by
        simpa only [MulAction.orbitRel.Quotient.orbit_mk] using W.orbit_card
      have heq := congrArg (fun q : Orbit H ↦ Nat.card q.orbit) hpoint
      have ho : Nat.card o.orbit = 16 := heq.symm.trans hmk
      simpa [halfSupport] using ho.symm

variable (hH : ResidualSector H)

/-- Total old support of the canonical retained-background profile, in
half-point units.  Zero-weight critical orbits are included literally. -/
def oldSupport : ℕ :=
  ∑ o : Orbit H, halfSupport (checkedProfile H hH o)

/-- On the canonical profile, a positive colour has its exact literal point
cost. -/
theorem doubled_checked_halfSupport_eq_orbit_card
    (o : Orbit H) (ho : (checkedProfile H hH o).IsPositive) :
    2 * halfSupport (checkedProfile H hH o) = Nat.card o.orbit :=
  doubled_halfSupport_eq_orbit_card_of_realizes H
    (profile_realizes H smallRegistryMixtureEquations hH o) ho

/-- Every colour, including a zero-weight critical colour, charges at most
the size of its literal original orbit. -/
theorem doubled_checked_halfSupport_le_orbit_card (o : Orbit H) :
    2 * halfSupport (checkedProfile H hH o) ≤ Nat.card o.orbit := by
  by_cases ho : (checkedProfile H hH o).IsPositive
  · exact (doubled_checked_halfSupport_eq_orbit_card H hH o ho).le
  · have hz : halfSupport (checkedProfile H hH o) = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hs
      exact ho ((isPositive_iff_halfSupport_pos _).2 hs)
    simp [hz]

/-- The structural positive-support predicate is exactly positivity of the
canonical numerical support. -/
theorem hasPositiveSupport_iff_oldSupport_pos :
    HasPositiveSupport H smallRegistryMixtureEquations hH ↔
      0 < oldSupport H hH := by
  constructor
  · rintro ⟨o,ho⟩
    unfold oldSupport
    apply Finset.sum_pos'
    · intro i hi
      exact Nat.zero_le _
    · refine ⟨o,Finset.mem_univ _,?_⟩
      exact (isPositive_iff_halfSupport_pos _).1 ho
  · intro hsum
    by_contra hpositive
    have hz : ∀ o : Orbit H,
        halfSupport (checkedProfile H hH o) = 0 := by
      intro o
      apply Nat.eq_zero_of_not_pos
      intro hs
      apply hpositive
      exact ⟨o,(isPositive_iff_halfSupport_pos _).2 hs⟩
    have hold : oldSupport H hH = 0 := by
      unfold oldSupport
      apply Finset.sum_eq_zero
      intro o ho
      exact hz o
    omega

/-- Literal positive support is bounded by the original half-degree. -/
theorem oldSupport_le_halfDegree (H : Subgroup (Equiv.Perm (Fin (2 * n))))
    (hH : ResidualSector H) :
    oldSupport H hH ≤ n := by
  have hdouble : 2 * oldSupport H hH ≤ 2 * n := by
    have horbits :
        (∑ o : Orbit H, Nat.card o.orbit) = Nat.card (Fin (2 * n)) := by
      rw [← Nat.card_sigma]
      exact Nat.card_congr
        (MulAction.selfEquivSigmaOrbits' H (Fin (2 * n))).symm
    calc
      2 * oldSupport H hH =
          ∑ o : Orbit H,
            2 * halfSupport (checkedProfile H hH o) := by
        unfold oldSupport
        rw [Finset.mul_sum]
      _ ≤ ∑ o : Orbit H, Nat.card o.orbit := by
        exact Finset.sum_le_sum (fun o _ ↦
          doubled_checked_halfSupport_le_orbit_card H hH o)
      _ = Nat.card (Fin (2 * n)) := horbits
      _ = 2 * n := by simp
  omega

/-! ## Fixed-support positive residual fibres -/

/-- The canonical support of an unmarked positive S16 residual subgroup. -/
def positiveResidualOldSupport {N : ℕ}
    (H : PositiveResidualFamily N) : ℕ :=
  oldSupport H.1.1 H.1.2

/-- Positive retained-background residuals with one fixed canonical old
support.  This is a subtype of the original unmarked family; no orbit or
route witness is stored. -/
abbrev PositiveResidualAtOldSupport (N Cold : ℕ) :=
  {H : PositiveResidualFamily N // positiveResidualOldSupport H = Cold}

theorem positiveResidualOldSupport_pos {N : ℕ}
    (H : PositiveResidualFamily N) :
    0 < positiveResidualOldSupport H :=
  (hasPositiveSupport_iff_oldSupport_pos H.1.1 H.1.2).1 H.2

theorem positiveResidualOldSupport_le {N : ℕ}
    (H : PositiveResidualFamily N) :
    positiveResidualOldSupport H ≤ N :=
  oldSupport_le_halfDegree H.1.1 H.1.2

end SymmetricSubgroupAsymptotics.BinaryS16SupportAccounting

end
