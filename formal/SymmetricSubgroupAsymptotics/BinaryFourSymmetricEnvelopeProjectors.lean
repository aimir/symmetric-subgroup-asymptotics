import SymmetricSubgroupAsymptotics.BinaryFourCanonicalOddMiddleChart
import SymmetricSubgroupAsymptotics.BinaryJordanPlusTrivialUniformGenerators
import SymmetricSubgroupAsymptotics.ModuleGeneratorProjectionSharing

/-! Exact seven-dimensional envelope after removing the binary bottom.
The C3 trace projects onto the actual reflection module P2 plus one scalar.
These identities apply to invariant subspaces without choosing complements
inside an original group extension. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

abbrev SymmetricEnvelope := (Fin 3 → Scalar) × (Local × Local)

def envelopeCycle (x : SymmetricEnvelope) : SymmetricEnvelope :=
  (x.1, localCycle x.2.1, localCycle x.2.2)

def envelopeReflection (x : SymmetricEnvelope) : SymmetricEnvelope :=
  (![x.1 1, x.1 0, x.1 2],
    ![x.2.1 0 + x.2.1 1, x.2.1 1], ![x.2.2 1, x.2.2 0])

def envelopeTrace (x : SymmetricEnvelope) : SymmetricEnvelope :=
  x + envelopeCycle x + envelopeCycle (envelopeCycle x)

theorem envelopeTrace_eq (x : SymmetricEnvelope) :
    envelopeTrace x = (x.1, 0, 0) := by
  revert x
  decide +kernel

theorem envelopeTrace_complement (x : SymmetricEnvelope) :
    x - envelopeTrace x = (0, x.2) := by
  revert x
  decide +kernel

theorem envelopeTrace_reflection (x : SymmetricEnvelope) :
    envelopeTrace (envelopeReflection x) = envelopeReflection (envelopeTrace x) := by
  revert x
  decide +kernel

theorem envelopeTrace_cycle (x : SymmetricEnvelope) :
    envelopeTrace (envelopeCycle x) = envelopeTrace x := by
  revert x
  decide +kernel

/-- Both projector components belong to the literal original invariant
subspace, rather than to a hypothetical split replacement. -/
theorem envelope_projector_mem
    (E : Submodule Scalar SymmetricEnvelope)
    (hc : ∀ x ∈ E, envelopeCycle x ∈ E)
    (x : SymmetricEnvelope) (hx : x ∈ E) :
    (x.1, (0 : Local), (0 : Local)) ∈ E ∧ (0, x.2) ∈ E := by
  have ht : envelopeTrace x ∈ E :=
    E.add_mem (E.add_mem hx (hc x hx)) (hc _ (hc x hx))
  constructor
  · simpa only [envelopeTrace_eq] using ht
  · simpa only [envelopeTrace_complement] using E.sub_mem hx ht

/-- The first component retains the exact canonical odd action on the
middle trivial pair, together with the additional sign-type top slot. -/
theorem envelopeReflection_trivial (a : Fin 3 → Scalar) :
    envelopeReflection (a, 0, 0) =
      (BinaryJordanPlusTrivialUniformGenerators.reflection a, 0, 0) := by
  revert a
  decide +kernel

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
