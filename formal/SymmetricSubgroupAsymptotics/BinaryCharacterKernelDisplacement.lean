import SymmetricSubgroupAsymptotics.PrimeCharacterKernelOrbits
import SymmetricSubgroupAsymptotics.RepresentationJointDisplacement

/-! The joint character-kernel budget for an actual section of the
original binary permutation module. Both the complete displacement slice
and the original point stabilizer are retained. Orbit counts and lengths
are proved from the original character evaluation, not supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k G X A V : Type} [Field k] [Group G] [MulAction G X]
    [Finite G] [Finite X] [MulAction.IsPretransitive G X]
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- The all-retained-character joint budget. The exponent j measures
exactly which retained characters kill the actual point stabilizer. -/
theorem binary_permutationSection_joint_character_kernel_bound
    (ρ : Representation k G A) (hG : IsPGroup 2 G)
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (χ : V →ₗ[ZMod 2] PrimeCharacters 2 G) (hχ : Function.Injective χ)
    (x : X) (a : ℕ) (hdegree : Nat.card X=2^a) :
    Module.finrank k ρ.invariants + Module.finrank k
      (displacementJointSlice ρ (retainedCharacterEvaluation 2 χ).ker) ≤
        2^(Module.finrank (ZMod 2) (retainedStabilizerVanishing 2 χ x)) *
          (a-Module.finrank (ZMod 2) (retainedStabilizerVanishing 2 χ x)).choose
            ((a-Module.finrank (ZMod 2) (retainedStabilizerVanishing 2 χ x))/2) := by
  exact permutationSection_displacementJoint_finrank_le_uniform_orbits
    ρ (retainedCharacterEvaluation 2 χ).ker hG M q hq
    (a-Module.finrank (ZMod 2) (retainedStabilizerVanishing 2 χ x))
    (Module.finrank (ZMod 2) (retainedStabilizerVanishing 2 χ x))
    (retainedCharacterKernel_orbit_classes_card 2 χ x hχ)
    (retainedCharacterKernel_orbit_card 2 χ x hχ a hdegree)

end SymmetricSubgroupAsymptotics
