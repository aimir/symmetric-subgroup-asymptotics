import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRankOneUniform

/-! Uniform one for every NONZERO actual odd kernel under A4/S4 block
image. The zero odd-kernel axis is exposed separately: a nonbinary top
does not imply a nonzero local odd kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingOddKernelUniform
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel

/-- Constant kernel classes use the actual rank-one chart; singleton
classes use actual kernel averages. No independent local cubic is assumed. -/
theorem uniform (C : Subgroup Frame)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (hO : oddKernel C≠⊥) : UniformSubrepresentationGeneratorBound
      (BinaryPlaneCyclicWreathUniform.representation C) 1 := by
  rcases BinaryPlaneAlternatingKernelPartition.zero_rankOne_or_distinct C heven with
    hzero | hrank | hdistinct
  · exact False.elim (hO hzero)
  · obtain ⟨e⟩ := hrank
    exact BinaryPlaneAlternatingRankOneUniform.uniform C e heven
  · exact BinaryPlaneAlternatingKernelPartition.distinct_uniform C heven hO hdistinct

/-- Honest branch interface: the unresolved zero-odd axis cannot be
silently folded into the nonbinary top case. -/
theorem zero_or_uniform (C : Subgroup Frame)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    oddKernel C=⊥ ∨ UniformSubrepresentationGeneratorBound
      (BinaryPlaneCyclicWreathUniform.representation C) 1 := by
  by_cases hO : oddKernel C=⊥
  · exact Or.inl hO
  · exact Or.inr (uniform C heven hO)

/-- The original retained subspace and literal quotient map survive the
uniform-one argument; no quotient-denominator replacement is used. -/
theorem section_uniform (C : Subgroup Frame)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (hO : oddKernel C≠⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (S : Subrepresentation (BinaryPlaneCyclicWreathUniform.representation C))
    (sigma : Representation (ZMod 2) C V)
    (q : Representation.IntertwiningMap S.toRepresentation sigma)
    (hq : Function.Surjective q) : UniformSubrepresentationGeneratorBound sigma 1 := by
  let inter : Representation.IntertwiningMap S.toRepresentation
      (BinaryPlaneCyclicWreathUniform.representation C) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' _ := rfl }
  exact ((uniform C heven hO).of_injective inter Subtype.val_injective).of_surjective q hq

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingOddKernelUniform
