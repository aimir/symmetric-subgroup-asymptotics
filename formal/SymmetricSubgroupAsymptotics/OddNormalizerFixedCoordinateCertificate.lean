import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.FiniteFrameOddNormalizerImporter

/-!
# Reversible coordinate certificates for odd-normalizer fixed spaces

A sixteen-block finite row need not enumerate all invariant submodules.
It supplies a reversible basis of the simultaneous fixed space and a linear
reconstruction identity modulo the displayed generator displacements.  The
identity proves that every fixed vector lies in the coordinate space; basis
checks prove the reverse containment.  This turns compact binary matrices
into the exact `FiniteFrameOddNormalizerWitness` consumed by the importer.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {G : Type} [Group G] [Finite G] {w r d : ℕ}
  (rho : Representation (ZMod 2) G (Fin w → ZMod 2))

/-- Compact, kernel-checkable data for one exact simultaneous fixed space.
The reconstruction formula is an unconditional linear identity, so an
exported certificate verifies it on the standard basis rather than ranging
over all `2^w` vectors. -/
structure BinaryOddNormalizerCoordinateCertificate : Type where
  A : Subgroup G
  generators : Fin r → G
  generated : Subgroup.closure (Set.range generators) = A
  odd_order : ¬ 2 ∣ Nat.card A
  g : G
  g_normalizes : g ∈ Subgroup.normalizer (A : Set G)
  g_order_two_power : ∃ a : ℕ, orderOf g = 2 ^ a
  coordinates : BinaryCoordinateSpace w d
  correctionGenerator : Fin r → Module.End (ZMod 2) (Fin w → ZMod 2)
  correctionNormalizer : Module.End (ZMod 2) (Fin w → ZMod 2)
  reconstruction : ∀ v,
    coordinates.inclusion (coordinates.coordinates v) =
      v + (∑ j, correctionGenerator j (rho (generators j) v - v)) +
        correctionNormalizer (rho g v - v)
  coordinate_generator_fixed : ∀ j i,
    rho (generators j) (coordinates.inclusion (Pi.single i 1)) =
      coordinates.inclusion (Pi.single i 1)
  coordinate_normalizer_fixed : ∀ i,
    rho g (coordinates.inclusion (Pi.single i 1)) =
      coordinates.inclusion (Pi.single i 1)

namespace BinaryOddNormalizerCoordinateCertificate

variable {rho : Representation (ZMod 2) G (Fin w → ZMod 2)}
  (C : BinaryOddNormalizerCoordinateCertificate
    (w := w) (r := r) (d := d) rho)

private theorem coordinate_space_generator_fixed
    (j : Fin r) (v : Fin w → ZMod 2) (hv : v ∈ C.coordinates.space) :
    rho (C.generators j) v = v := by
  let W := representationElementFixedSpace rho (C.generators j)
  have hle : C.coordinates.space ≤ W := by
    apply C.coordinates.le_of_basis_mem
    intro i
    exact (mem_representationElementFixedSpace _ _ _).mpr
      (C.coordinate_generator_fixed j i)
  exact (mem_representationElementFixedSpace _ _ _).mp (hle hv)

private theorem coordinate_space_A_fixed
    (v : Fin w → ZMod 2) (hv : v ∈ C.coordinates.space)
    (a : C.A) : rho a.1 v = v := by
  let S : Subgroup G := {
    carrier := {x | rho x v = v}
    one_mem' := by simp
    mul_mem' := by
      intro x y hx hy
      change rho (x * y) v = v
      rw [map_mul]
      change rho x (rho y v) = v
      rw [hy, hx]
    inv_mem' := by
      intro x hx
      have hcancel : rho x⁻¹ (rho x v) = v := by
        change (rho x⁻¹ * rho x) v = v
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      rwa [hx] at hcancel }
  have hgen : Set.range C.generators ⊆ S := by
    rintro _ ⟨j, rfl⟩
    change rho (C.generators j) v = v
    exact C.coordinate_space_generator_fixed j v hv
  have hA : C.A ≤ S := by
    rw [← C.generated]
    exact (Subgroup.closure_le S).mpr hgen
  have haS : a.1 ∈ S := hA a.2
  change rho a.1 v = v at haS
  exact haS

private theorem coordinate_space_g_fixed
    (v : Fin w → ZMod 2) (hv : v ∈ C.coordinates.space) :
    rho C.g v = v := by
  let W := representationElementFixedSpace rho C.g
  have hle : C.coordinates.space ≤ W := by
    apply C.coordinates.le_of_basis_mem
    intro i
    exact (mem_representationElementFixedSpace _ _ _).mpr
      (C.coordinate_normalizer_fixed i)
  exact (mem_representationElementFixedSpace _ _ _).mp (hle hv)

/-- The reversible coordinate space is exactly the simultaneous fixed space
of the retained odd subgroup and normalizer element. -/
theorem coordinate_space_eq_oddNormalizerFixedSpace :
    C.coordinates.space = oddNormalizerFixedSpace rho C.A C.g := by
  apply le_antisymm
  · intro v hv
    exact ⟨(Representation.mem_invariants
        (ρ := rho.comp C.A.subtype) v).mpr
          (C.coordinate_space_A_fixed v hv),
      (mem_representationElementFixedSpace rho C.g v).mpr
        (C.coordinate_space_g_fixed v hv)⟩
  · intro v hv
    apply (C.coordinates.mem_iff v).mpr
    have hgen : ∀ j, rho (C.generators j) v = v := by
      intro j
      have hj : C.generators j ∈ C.A := by
        rw [← C.generated]
        exact Subgroup.subset_closure ⟨j, rfl⟩
      exact (Representation.mem_invariants
        (ρ := rho.comp C.A.subtype) v).mp hv.1 ⟨C.generators j, hj⟩
    have hg := (mem_representationElementFixedSpace rho C.g v).mp hv.2
    rw [C.reconstruction v]
    simp [hgen, hg]

/-- The compact coordinate certificate produces the exact witness retained
by a sixteen-frame row. -/
noncomputable def toOddNormalizerWitness :
    FiniteFrameOddNormalizerWitness rho where
  A := C.A
  odd_order := C.odd_order
  g := C.g
  g_normalizes := C.g_normalizes
  g_order_two_power := C.g_order_two_power
  fixed := oddNormalizerFixedSpace rho C.A C.g
  mem_fixed_iff := by
    intro v
    change (v ∈ Representation.invariants (rho.comp C.A.subtype) ∧
      v ∈ representationElementFixedSpace rho C.g) ↔ _
    rw [Representation.mem_invariants,
      mem_representationElementFixedSpace]
    rfl
  dimension := d
  dimension_eq := by
    rw [← C.coordinate_space_eq_oddNormalizerFixedSpace]
    exact C.coordinates.finrank

end BinaryOddNormalizerCoordinateCertificate

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
