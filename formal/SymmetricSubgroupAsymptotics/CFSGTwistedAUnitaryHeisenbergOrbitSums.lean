import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergOrbits

/-! Sum the exact Heisenberg divisibility over the ACTUAL radical
orbits. The carrier here has no centre-fixed points; it will be the
invariant nonfixed part of the original permutation action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGCentralTransitiveAction
open MulAction

def fixedBySigmaOrbitsEquiv {G X : Type*} [Group G] [MulAction G X]
    (C : Subgroup G) (c : C) :
    fixedBy X c ≃ Σ o : Quotient (orbitRel G X), fixedBy (orbitRel.Quotient.orbit o) c where
  toFun x := ⟨Quotient.mk'' x.val,
    ⟨⟨x.val, orbitRel.Quotient.mem_orbit.mpr rfl⟩, Subtype.ext x.property⟩⟩
  invFun x := ⟨x.2.val.val, congrArg Subtype.val x.2.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := by
    rcases x with ⟨o, ⟨⟨x, hx⟩, hfix⟩⟩
    have ho : (Quotient.mk'' x : Quotient (orbitRel G X)) = o :=
      orbitRel.Quotient.mem_orbit.mp hx
    subst o
    rfl

end SymmetricSubgroupAsymptotics.CFSGCentralTransitiveAction

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open MulAction

def radicalOrbitBase (q : CFSG.PrimePower) (s : ℕ) {X : Type*}
    [MulAction (fixedRadical q s) X]
    (o : Quotient (orbitRel (fixedRadical q s) X)) : orbitRel.Quotient.orbit o :=
  ⟨o.out, orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' o)⟩

theorem radicalOrbit_stabilizer_misses {X : Type*} (q : CFSG.PrimePower) (s : ℕ)
    [MulAction (fixedRadical q s) X]
    (hnone : ∀ x : X, ¬ radicalCentre q s ≤ stabilizer (fixedRadical q s) x)
    (o : Quotient (orbitRel (fixedRadical q s) X)) (x : orbitRel.Quotient.orbit o) :
    ¬ radicalCentre q s ≤ stabilizer (fixedRadical q s) x := by
  intro hh
  apply hnone x.val
  intro c hc
  exact congrArg Subtype.val (hh hc)

theorem radical_moving_degree_divisibility {X : Type*} (q : CFSG.PrimePower) (s : ℕ)
    [MulAction (fixedRadical q s) X] [Finite X]
    (hnone : ∀ x : X, ¬ radicalCentre q s ≤ stabilizer (fixedRadical q s) x) :
    q.order ^ (s + 1) ∣ Nat.card X := by
  letI : Fintype (Quotient (orbitRel (fixedRadical q s) X)) := Fintype.ofFinite _
  have he := Nat.card_congr (selfEquivSigmaOrbits' (fixedRadical q s) X)
  rw [he, Nat.card_sigma]
  apply Finset.dvd_sum
  intro o _
  exact radical_transitive_divisibility q s (radicalOrbitBase q s o)
    (radicalOrbit_stabilizer_misses q s hnone o _)

theorem radical_moving_fixedBy_divisibility {X : Type*} (q : CFSG.PrimePower) (s : ℕ)
    [MulAction (fixedRadical q s) X] [Finite X]
    (hnone : ∀ x : X, ¬ radicalCentre q s ≤ stabilizer (fixedRadical q s) x)
    (c : radicalCentre q s) : q.order ^ (s + 1) ∣ Nat.card (fixedBy X c) := by
  letI : Fintype (Quotient (orbitRel (fixedRadical q s) X)) := Fintype.ofFinite _
  have he := Nat.card_congr (CFSGCentralTransitiveAction.fixedBySigmaOrbitsEquiv
    (G := fixedRadical q s) (X := X) (radicalCentre q s) c)
  rw [he, Nat.card_sigma]
  apply Finset.dvd_sum
  intro o _
  exact radical_transitive_fixedBy_divisibility q s (radicalOrbitBase q s o)
    (radicalOrbit_stabilizer_misses q s hnone o _) c

theorem radical_moving_orbit_divisibility {X : Type*} (q : CFSG.PrimePower) (s : ℕ)
    [MulAction (fixedRadical q s) X] [Finite X]
    (hnone : ∀ x : X, ¬ radicalCentre q s ≤ stabilizer (fixedRadical q s) x) :
    q.order ^ (s + 1) ∣ Nat.card (Quotient (orbitRel (radicalCentre q s) X)) := by
  letI : Fintype (Quotient (orbitRel (fixedRadical q s) X)) := Fintype.ofFinite _
  have he := Nat.card_congr (equivSubgroupOrbits X (radicalCentre q s))
  rw [he, Nat.card_sigma]
  apply Finset.dvd_sum
  intro o _
  exact radical_transitive_orbit_divisibility q s (radicalOrbitBase q s o)
    (radicalOrbit_stabilizer_misses q s hnone o _)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
