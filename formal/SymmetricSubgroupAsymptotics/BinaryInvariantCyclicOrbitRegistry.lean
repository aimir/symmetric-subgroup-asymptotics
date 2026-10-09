import SymmetricSubgroupAsymptotics.BinaryInvariantOrbitRegistry
import SymmetricSubgroupAsymptotics.FiniteLinearOrbitCardinalCover

/-!
# Vector-orbit covers with deduplicated cyclic joins

The eight-block frame calculation has two distinct finite quotients of the
ambient vector space:

* actual vector orbits, which certify that every point is represented; and
* cyclic invariant submodules, which determine the join transition.

Different vector orbits can generate the same cyclic invariant submodule.
Keeping these indices separate is the practical certificate format: the
orbit cover has one row per vector orbit, while the child table has only one
column per distinct cyclic submodule.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k G V I : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- A complete invariant-axis registry with separate vector-orbit and
cyclic-submodule indices. -/
structure BinaryInvariantCyclicOrbitRegistry
    (rho : Representation k G V)
    (states : I → Subrepresentation rho) where
  Orbit : Type
  [orbitFinite : Finite Orbit]
  orbitRepresentative : Orbit → V
  orbitRepresentative_complete :
    ∀ v : V, ∃ o g, rho g (orbitRepresentative o) = v
  Cyclic : Type
  [cyclicFinite : Finite Cyclic]
  cyclicRepresentative : Cyclic → V
  orbitCyclic : Orbit → Cyclic
  orbit_span_eq : ∀ o,
    binaryOrbitSpan rho (orbitRepresentative o) =
      binaryOrbitSpan rho (cyclicRepresentative (orbitCyclic o))
  bottom : I
  bottom_eq : (states bottom).toSubmodule = ⊥
  child : I → Cyclic → I
  child_eq : ∀ i c, (states (child i c)).toSubmodule =
    (states i).toSubmodule ⊔ binaryOrbitSpan rho (cyclicRepresentative c)

attribute [instance]
  BinaryInvariantCyclicOrbitRegistry.orbitFinite
  BinaryInvariantCyclicOrbitRegistry.cyclicFinite

namespace BinaryInvariantCyclicOrbitRegistry

variable {rho : Representation k G V}
  {states : I → Subrepresentation rho}
  (C : BinaryInvariantCyclicOrbitRegistry rho states)

/-- Build the orbit-cover field from pairwise separation and the exact sum
of orbit cardinalities.  Generated rows therefore store one cardinality per
orbit, rather than one predecessor path per vector. -/
noncomputable def ofCardinalCover [Finite V] {c d : ℕ}
    (orbitRepresentative : Fin c → V)
    (orbitCover : FiniteLinearOrbitCardinalCover rho orbitRepresentative)
    (cyclicRepresentative : Fin d → V)
    (orbitCyclic : Fin c → Fin d)
    (orbit_span_eq : ∀ o,
      binaryOrbitSpan rho (orbitRepresentative o) =
        binaryOrbitSpan rho (cyclicRepresentative (orbitCyclic o)))
    (bottom : I) (bottom_eq : (states bottom).toSubmodule = ⊥)
    (child : I → Fin d → I)
    (child_eq : ∀ i c, (states (child i c)).toSubmodule =
      (states i).toSubmodule ⊔ binaryOrbitSpan rho (cyclicRepresentative c)) :
    BinaryInvariantCyclicOrbitRegistry rho states where
  Orbit := Fin c
  orbitRepresentative := orbitRepresentative
  orbitRepresentative_complete := orbitCover.covers
  Cyclic := Fin d
  cyclicRepresentative := cyclicRepresentative
  orbitCyclic := orbitCyclic
  orbit_span_eq := orbit_span_eq
  bottom := bottom
  bottom_eq := bottom_eq
  child := child
  child_eq := child_eq

include C

/-- Expand only from cyclic-submodule columns to vector-orbit columns.  This
is a logical adapter; generated source retains the smaller child table. -/
noncomputable def toOrbitRegistry :
    BinaryInvariantOrbitRegistry rho states where
  Orbit := C.Orbit
  representative := C.orbitRepresentative
  representative_complete := C.orbitRepresentative_complete
  bottom := C.bottom
  bottom_eq := C.bottom_eq
  child i o := C.child i (C.orbitCyclic o)
  child_eq i o := by
    rw [C.child_eq, C.orbit_span_eq]

/-- A cyclic-orbit registry covers every invariant submodule. -/
theorem complete [Finite V] (W : Subrepresentation rho) :
    ∃ i, states i = W :=
  C.toOrbitRegistry.complete W

/-! ## Canonical semantic registry -/

/-- The full orbit span of one vector, packaged as an invariant
subrepresentation. -/
def orbitSubrepresentation (rho : Representation k G V) (v : V) :
    Subrepresentation rho where
  toSubmodule := binaryOrbitSpan rho v
  apply_mem_toSubmodule g x hx := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨h, rfl⟩ := hy
        change rho g (rho h v) ∈ binaryOrbitSpan rho v
        rw [← Module.End.mul_apply, ← map_mul]
        exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
        simpa only [map_add] using
          (binaryOrbitSpan rho v).add_mem hx hy
    | smul a x _ hx =>
        simpa only [map_smul] using
          (binaryOrbitSpan rho v).smul_mem a hx

/-- For a finite module, the type of invariant subrepresentations is
finite.  This instance is intentionally noncomputable; compressed producer
tables may replace it when exact state counts are useful. -/
noncomputable instance allSubrepresentationsFinite [Finite V] :
    Finite (Subrepresentation rho) :=
  Finite.of_injective
    (fun W : Subrepresentation rho => (W : Set V)) SetLike.coe_injective

/-- A census-free complete registry whose states are all invariant
subrepresentations and whose orbit/cyclic indices are the vectors
themselves.  It is a small-width semantic fallback and a useful pilot target
for generated compressed registries: completeness follows from the general
join theorem, not from an asserted producer flag. -/
noncomputable def allSubrepresentations [Finite V] :
    BinaryInvariantCyclicOrbitRegistry rho
      (fun W : Subrepresentation rho => W) where
  Orbit := V
  orbitRepresentative := id
  orbitRepresentative_complete v := ⟨v, 1, by simp⟩
  Cyclic := V
  cyclicRepresentative := id
  orbitCyclic := id
  orbit_span_eq := fun _ => rfl
  bottom := ⊥
  bottom_eq := rfl
  child W v := W ⊔ orbitSubrepresentation rho v
  child_eq := fun _ _ => rfl

end BinaryInvariantCyclicOrbitRegistry

end SymmetricSubgroupAsymptotics

end
