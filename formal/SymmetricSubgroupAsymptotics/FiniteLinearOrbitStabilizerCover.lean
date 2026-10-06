import SymmetricSubgroupAsymptotics.FiniteLinearOrbitCardinalCover
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Sparse linear-orbit coverage from stabilizer orders

For an executable finite matrix group, checking a stabilizer order is much
smaller than enumerating the whole orbit in the generated Lean source.  This
file packages the orbit-stabilizer conversion needed by the eight-frame
importer.  The certificate still refers to the literal stabilizer subgroup
of the literal representation; the supplied cardinalities are not trusted
labels.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {k G V : Type*} [Field k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [Finite V] {c : ℕ}

/-- The literal stabilizer of a vector under a displayed representation,
without installing a competing global scalar-action instance. -/
def representationVectorStabilizer
    (rho : Representation k G V) (v : V) : Subgroup G where
  carrier := {g | rho g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change rho g v = v at hg
    change rho h v = v at hh
    change rho (g * h) v = v
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change rho g v = v at hg
    change rho g⁻¹ v = v
    apply (rho.apply_bijective g).injective
    rw [Representation.self_inv_apply, hg]

/-- Pairwise distinct representatives together with checked stabilizer
orders.  The displayed arithmetic sum is the sparse finite exhaustion test.
-/
structure FiniteLinearOrbitStabilizerCover
    (rho : Representation k G V) (representative : Fin c → V) : Type 1 where
  separated : ∀ i j,
    (∃ g : G, rho g (representative i) = representative j) → i = j
  stabilizerCard : Fin c → ℕ
  stabilizer_card : ∀ i,
    Nat.card (representationVectorStabilizer rho (representative i)) =
      stabilizerCard i
  orbit_card_sum :
    (∑ i : Fin c, Nat.card G / stabilizerCard i) = Nat.card V

namespace FiniteLinearOrbitStabilizerCover

variable {rho : Representation k G V} {representative : Fin c → V}
  (C : FiniteLinearOrbitStabilizerCover rho representative)

include C

/-- Orbit-stabilizer turns each checked stabilizer order into the literal
orbit cardinality required by `FiniteLinearOrbitCardinalCover`. -/
theorem orbit_card (i : Fin c) :
    Nat.card {v : V // ∃ g : G, rho g (representative i) = v} =
      Nat.card G / C.stabilizerCard i := by
  classical
  letI : SMul G V := ⟨fun g v ↦ rho g v⟩
  letI : MulAction G V := {
    one_smul v := by
      change rho 1 v = v
      rw [map_one]
      rfl
    mul_smul g h v := by
      change rho (g * h) v = rho g (rho h v)
      rw [map_mul, Module.End.mul_apply]
  }
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (MulAction.orbit G (representative i)) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer G (representative i)) :=
    Fintype.ofFinite _
  let e : MulAction.orbit G (representative i) ≃
      {v : V // ∃ g : G, rho g (representative i) = v} :=
    { toFun := fun v ↦ ⟨v, v.property⟩
      invFun := fun v ↦ ⟨v, v.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hmul :
      Nat.card {v : V // ∃ g : G, rho g (representative i) = v} *
          Nat.card (MulAction.stabilizer G (representative i)) = Nat.card G := by
    rw [← Nat.card_congr e]
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        G (representative i)
  have hstabilizer :
      Nat.card (MulAction.stabilizer G (representative i)) =
        C.stabilizerCard i := by
    change Nat.card
        (representationVectorStabilizer rho (representative i)) = _
    exact C.stabilizer_card i
  rw [hstabilizer] at hmul
  exact Nat.eq_div_of_mul_eq_left
    (by
      rw [← hstabilizer]
      exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
    hmul

/-- Forget the checked stabilizer orders after deriving the literal orbit
cardinalities. -/
def toCardinalCover : FiniteLinearOrbitCardinalCover rho representative where
  separated := C.separated
  orbit_card_sum := by
    simpa only [C.orbit_card] using C.orbit_card_sum

end FiniteLinearOrbitStabilizerCover
end SymmetricSubgroupAsymptotics

end
