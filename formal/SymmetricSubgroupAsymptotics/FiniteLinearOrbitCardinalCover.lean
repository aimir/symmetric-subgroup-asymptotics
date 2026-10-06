import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Sparse linear-orbit coverage from cardinalities

A finite module orbit cover should not list one path for every vector.  A
pairwise separated representative list is complete once the sum of its
literal orbit cardinalities equals the cardinality of the module.  This is
the linear-action analogue of `FiniteConjugacyCardinalCover`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [Finite V] {c : ℕ}

/-- Pairwise distinct linear orbits whose cardinalities exhaust the finite
module. -/
structure FiniteLinearOrbitCardinalCover
    (rho : Representation k G V) (representative : Fin c → V) : Prop where
  separated : ∀ i j,
    (∃ g : G, rho g (representative i) = representative j) → i = j
  orbit_card_sum :
    (∑ i : Fin c,
      Nat.card {v : V // ∃ g : G, rho g (representative i) = v}) =
      Nat.card V

namespace FiniteLinearOrbitCardinalCover

variable {rho : Representation k G V} {representative : Fin c → V}
  (C : FiniteLinearOrbitCardinalCover rho representative)

/-- Forget the selected orbit label and retain its vector. -/
def coverMap :
    (Σ i : Fin c, {v : V // ∃ g : G, rho g (representative i) = v}) → V
  | ⟨_, v⟩ => v

include C

omit [Finite V] in
theorem coverMap_injective :
    Function.Injective (coverMap (rho := rho) (representative := representative)) := by
  intro x y hxy
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  have hval : (x : V) = (y : V) := by
    simpa only [coverMap] using hxy
  obtain ⟨g, hg⟩ := x.property
  obtain ⟨h, hh⟩ := y.property
  have horbit : ∃ a : G, rho a (representative i) = representative j := by
    refine ⟨h⁻¹ * g, ?_⟩
    rw [map_mul, Module.End.mul_apply, hg, hval, ← hh,
      ← Module.End.mul_apply, ← map_mul]
    simp
  have hij : i = j := C.separated i j horbit
  subst j
  have hsub : x = y := Subtype.ext hval
  subst y
  rfl

/-- The cardinality identity upgrades the disjoint selected orbits to a
surjective cover of the whole module. -/
theorem coverMap_surjective :
    Function.Surjective
      (coverMap (rho := rho) (representative := representative)) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI (i : Fin c) : Fintype
      {v : V // ∃ g : G, rho g (representative i) = v} :=
    Fintype.ofFinite _
  by_contra hsurj
  have hlt := Fintype.card_lt_of_injective_not_surjective
    (coverMap (rho := rho) (representative := representative))
    C.coverMap_injective hsurj
  have heq :
      Fintype.card
          (Σ i : Fin c, {v : V // ∃ g : G,
            rho g (representative i) = v}) =
        Fintype.card V := by
    rw [Fintype.card_sigma]
    simpa only [Nat.card_eq_fintype_card] using C.orbit_card_sum
  exact (ne_of_lt hlt) heq

/-- Every vector is carried from one selected representative by an actual
group element. -/
theorem covers (v : V) :
    ∃ i : Fin c, ∃ g : G, rho g (representative i) = v := by
  obtain ⟨⟨i, x⟩, hx⟩ := C.coverMap_surjective v
  refine ⟨i, ?_⟩
  obtain ⟨g, hg⟩ := x.property
  have hxval : (x : V) = v := by
    simpa only [coverMap] using hx
  exact ⟨g, hg.trans hxval⟩

end FiniteLinearOrbitCardinalCover
end SymmetricSubgroupAsymptotics

end
