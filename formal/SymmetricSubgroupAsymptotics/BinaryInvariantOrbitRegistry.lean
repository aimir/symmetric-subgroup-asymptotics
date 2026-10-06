import SymmetricSubgroupAsymptotics.BinaryInvariantRegistry

/-!
# Compressed invariant-submodule registries

The finite eight-block frame calculation has `2^16` vectors, but only
21,892 vector orbits across its thirty rows.  A complete certificate should
therefore record one cyclic extension per orbit, rather than repeat the same
extension for every vector in an orbit.

`BinaryInvariantOrbitRegistry` is the exact compressed replacement.  Its
`representative_complete` field is a finite orbit-cover check.  The theorem
`toRegistry` expands that check logically (not as generated data) to the
pointwise `BinaryInvariantRegistry` interface, so the existing completeness
proof remains unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k G V I : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- Acting on the chosen generator does not change its full orbit span. -/
theorem binaryOrbitSpan_action (rho : Representation k G V) (g : G) (v : V) :
    binaryOrbitSpan rho (rho g v) = binaryOrbitSpan rho v := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    apply Submodule.subset_span
    refine ⟨h * g, ?_⟩
    simp only [map_mul, Module.End.mul_apply]
  · apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    apply Submodule.subset_span
    refine ⟨h * g⁻¹, ?_⟩
    simp only [map_mul, Module.End.mul_apply]
    simp

/-- A complete invariant-axis registry compressed by actual vector orbits.

The orbit representatives and their cover are part of the checked finite
certificate.  Only one child transition is stored for each representative.
This logical interface is covered by the 21,892 orbit rows.  The practical
generated format below deduplicates orbit spans before storing the 39,449
state/cyclic-submodule joins checked by
`computations/frames/verify_modules8.py`.
-/
structure BinaryInvariantOrbitRegistry (rho : Representation k G V)
    (states : I → Subrepresentation rho) where
  Orbit : Type
  [orbitFinite : Finite Orbit]
  representative : Orbit → V
  representative_complete : ∀ v : V, ∃ o g, rho g (representative o) = v
  bottom : I
  bottom_eq : (states bottom).toSubmodule = ⊥
  child : I → Orbit → I
  child_eq : ∀ i o, (states (child i o)).toSubmodule =
    (states i).toSubmodule ⊔ binaryOrbitSpan rho (representative o)

attribute [instance] BinaryInvariantOrbitRegistry.orbitFinite

namespace BinaryInvariantOrbitRegistry

variable {rho : Representation k G V}
  {states : I → Subrepresentation rho}
  (C : BinaryInvariantOrbitRegistry rho states)

include C

private noncomputable def orbitIndex (v : V) : C.Orbit :=
  Classical.choose (C.representative_complete v)

private noncomputable def orbitElement (v : V) : G :=
  Classical.choose (Classical.choose_spec (C.representative_complete v))

private theorem orbitElement_spec (v : V) :
    rho (C.orbitElement v) (C.representative (C.orbitIndex v)) = v :=
  Classical.choose_spec (Classical.choose_spec (C.representative_complete v))

/-- Expand the orbit-compressed transitions to the existing pointwise
registry interface.  No table is expanded in the generated source. -/
noncomputable def toRegistry : BinaryInvariantRegistry rho states where
  bottom := C.bottom
  bottom_eq := C.bottom_eq
  child i v := C.child i (C.orbitIndex v)
  child_eq i v := by
    rw [C.child_eq]
    congr 1
    calc
      binaryOrbitSpan rho (C.representative (C.orbitIndex v)) =
          binaryOrbitSpan rho
            (rho (C.orbitElement v) (C.representative (C.orbitIndex v))) :=
        (binaryOrbitSpan_action rho (C.orbitElement v)
          (C.representative (C.orbitIndex v))).symm
      _ = binaryOrbitSpan rho v :=
        congrArg (binaryOrbitSpan rho) (C.orbitElement_spec v)

/-- Orbit-compressed local joins still cover every invariant submodule. -/
theorem complete [Finite V] (W : Subrepresentation rho) :
    ∃ i, states i = W :=
  C.toRegistry.complete W

end BinaryInvariantOrbitRegistry

end SymmetricSubgroupAsymptotics

end
