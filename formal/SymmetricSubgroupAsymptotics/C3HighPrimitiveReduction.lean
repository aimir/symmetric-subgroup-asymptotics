import SymmetricSubgroupAsymptotics.C3HighOrbitDichotomy
import SymmetricSubgroupAsymptotics.C1PrimitiveTail
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage

/-!
# Primitive-tail reduction for the high C3 orbit pair

The published primitive normal-generator input is stated for labelled
subgroups of `S_w`.  The first theorem transports it to an arbitrary actual
finite faithful primitive action, carrying the original normal subgroup and
its ambient relative-character action through the same labelling.

It follows that the orbit pair forced by a high C3 state may be chosen with
either imprimitive ambient action or degree below 34.  This is exactly the
entry point for the finite primitive menu and the minimal-block recurrence.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The degree-34 primitive tail on an arbitrary literal finite faithful
action.  Relabelling does not replace either the ambient group or the normal
pair: both are carried by an actual group equivalence. -/
theorem c1_primitive_relative_tail_faithful
    (hgen : PrimitiveNormalGeneratorInput)
    {A Ω : Type} [Group A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPreprimitive A Ω]
    (hw : 34 ≤ Nat.card Ω) (N : Subgroup A) [N.Normal] :
    20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) <
      3 * Nat.card Ω := by
  let w := Nat.card Ω
  let e : Ω ≃ Fin w := Finite.equivFin Ω
  letI : Finite A := faithfulLabelledAction_finite e
  have hprim : MulAction.IsPreprimitive
      (labelledActionImage (A := A) e) (Fin w) :=
    (labelledAction_preprimitive_iff e).mp inferInstance
  have htail := c1_primitive_relative_tail hgen w hw
    (labelledActionImage (A := A) e) hprim (labelledActionNormal e N)
  rw [← labelledActionNormal_head e 3 N] at htail
  exact htail

/-- A high C3 state has a high actual orbit pair whose ambient transitive
action is imprimitive or has degree at most 33. -/
theorem c3TrivialHigh_primitive_reduction
    (hgen : PrimitiveNormalGeneratorInput) (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (hH : C3TrivialHighPredicate b P H) :
    ∃ o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H),
      ∃ (N : Subgroup
          (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o))
        (hN : N.Normal),
        (3 * Nat.card o.orbit <
          20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) ∧
        (Nat.card o.orbit < 34 ∨
          ¬ MulAction.IsPreprimitive
            (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o)
            o.orbit) := by
  obtain ⟨o, N, hN, hhigh⟩ := c3TrivialHigh_actualOrbit_witness b P H hH
  refine ⟨o, N, hN, hhigh, ?_⟩
  by_cases hsmall : Nat.card o.orbit < 34
  · exact Or.inl hsmall
  right
  intro hprimitive
  letI : MulAction.IsPreprimitive
      (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o) o.orbit :=
    hprimitive
  letI : N.Normal := hN
  have htail := c1_primitive_relative_tail_faithful hgen
    (A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o)
    (Ω := o.orbit) (by omega) N
  omega

end SymmetricSubgroupAsymptotics

end
