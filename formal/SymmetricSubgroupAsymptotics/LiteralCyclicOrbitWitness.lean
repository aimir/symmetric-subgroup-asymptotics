import SymmetricSubgroupAsymptotics.PermutationPolynomialOrbitGenerators
import Mathlib.Data.Fin.Embedding

/-!
# Literal point witnesses for uniform permutation-module generators

The witness is indexed by the exact subgroup of the original symmetric
group. It assigns each point a representative and a bounded exponent, so
the finite certificate consists of one displayed equality per point.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A literal cyclic orbit cover of the original point action. No group
order, vector census, or invariant-subspace enumeration is part of the data. -/
structure LiteralCyclicOrbitWitness {d : ℕ}
    (T : Subgroup (Equiv.Perm (Fin d))) (r : ℕ) where
  element : T
  representative : Fin r → Fin d
  orbitIndex : Fin d → Fin r
  exponent : Fin d → Fin d
  point_eq : ∀ x : Fin d,
    (element.val ^ (exponent x).val) (representative (orbitIndex x)) = x

namespace LiteralCyclicOrbitWitness

variable {d r : ℕ} {T : Subgroup (Equiv.Perm (Fin d))}
    (C : LiteralCyclicOrbitWitness T r)

/-- The explicit point assignments supply the cover expected by the
polynomial-module theorem. -/
theorem orbit_cover : ∀ x : Fin d,
    ∃ (j : Fin r) (m : ℕ), C.element ^ m • C.representative j = x := by
  intro x
  exact ⟨C.orbitIndex x, (C.exponent x).val, C.point_eq x⟩

include C in
/-- An exact-top point witness bounds every invariant subspace over any
field, including fields whose characteristic divides the element order. -/
theorem uniform (k : Type) [Field k] :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k T (Fin d)) r :=
  permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    C.element C.representative C.orbit_cover

/-- Reindex the representative positions through an embedding, filling
unused positions by any point. The assigned orbit positions do not change. -/
noncomputable def reindex {s : ℕ} (e : Fin r ↪ Fin s) (fallback : Fin d) :
    LiteralCyclicOrbitWitness T s where
  element := C.element
  representative := Function.extend e C.representative (fun _ ↦ fallback)
  orbitIndex x := e (C.orbitIndex x)
  exponent := C.exponent
  point_eq x := by
    rw [e.injective.extend_apply]
    exact C.point_eq x

/-- Pad a witness to a larger generator budget without manual casts of
point assignments. A nonempty point set supplies the unused representative. -/
noncomputable def pad [NeZero d] {s : ℕ} (h : r ≤ s) :
    LiteralCyclicOrbitWitness T s :=
  C.reindex (Fin.castLEEmb h) 0

include C in
/-- The padded generator bound at the same exact top. -/
theorem uniform_of_le [NeZero d] (k : Type) [Field k] {s : ℕ} (h : r ≤ s) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k T (Fin d)) s :=
  (C.pad h).uniform k

/-- A subgroup inclusion transports the same literal permutation and point
assignments to the larger exact top, without changing coordinates. -/
def enlargeTop {S : Subgroup (Equiv.Perm (Fin d))} (h : T ≤ S) :
    LiteralCyclicOrbitWitness S r where
  element := ⟨C.element.val, h C.element.property⟩
  representative := C.representative
  orbitIndex := C.orbitIndex
  exponent := C.exponent
  point_eq := C.point_eq

end LiteralCyclicOrbitWitness
end SymmetricSubgroupAsymptotics

end
