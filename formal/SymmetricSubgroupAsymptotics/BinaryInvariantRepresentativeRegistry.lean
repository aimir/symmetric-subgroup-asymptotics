import SymmetricSubgroupAsymptotics.BinaryInvariantRegistry

/-! A complete invariant registry can retain one point for each actual
cyclic orbit-space. Point-to-representative equalities are proved once;
local joins then need only the retained cyclic representatives. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k G V I C : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V]

/-- A finite certificate compressing points by their actual orbit-span,
while preserving every original invariant subspace. -/
structure BinaryInvariantRepresentativeRegistry
    (rho : Representation k G V) (states : I → Subrepresentation rho) where
  representative : C → V
  pointClass : V → C
  point_span : ∀ v,
    binaryOrbitSpan rho v = binaryOrbitSpan rho (representative (pointClass v))
  bottom : I
  bottom_eq : (states bottom).toSubmodule = ⊥
  child : I → C → I
  child_eq : ∀ i c,
    (states (child i c)).toSubmodule =
      (states i).toSubmodule ⊔ binaryOrbitSpan rho (representative c)

namespace BinaryInvariantRepresentativeRegistry

variable {rho : Representation k G V} {states : I → Subrepresentation rho}
  (R : BinaryInvariantRepresentativeRegistry (C := C) rho states)

include R

/-- The compressed certificate supplies every literal point-adjunction
required by the existing invariant-registry theorem. -/
def toRegistry : BinaryInvariantRegistry rho states where
  bottom := R.bottom
  bottom_eq := R.bottom_eq
  child i v := R.child i (R.pointClass v)
  child_eq i v := by
    rw [R.child_eq, R.point_span v]

/-- No assertion of finite-list completeness is assumed: it follows from
the checked point-span equalities and representative joins. -/
theorem complete [Finite V] (W : Subrepresentation rho) : ∃ i, states i = W :=
  R.toRegistry.complete W

end BinaryInvariantRepresentativeRegistry

end SymmetricSubgroupAsymptotics
