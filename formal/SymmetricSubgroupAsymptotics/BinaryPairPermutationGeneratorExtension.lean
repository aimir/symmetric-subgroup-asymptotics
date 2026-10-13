import SymmetricSubgroupAsymptotics.BinaryPairSectionSchurCapacity
import SymmetricSubgroupAsymptotics.BinaryPairMaximalSection
import SymmetricSubgroupAsymptotics.PermutationFunctionSelfDual
import SymmetricSubgroupAsymptotics.RepresentationGeneratorExtension

/-!
# Generator bounds for a permutation module on pairs

For a binary pair frame, the permutation module on the points is an exact
extension of the permutation module on the pairs by a second copy of the
same pair module.  The left map is `pairConstant`; the right map is
`pairSum`.  Combining this literal exact sequence with the general
extension theorem doubles any uniform generator bound on the pair module.

This is the reusable semantic bridge needed by the two-frame paired-eight
degree-two rows.  It applies to every actual outer pair action and therefore
does not require choosing one of the older sixteen-dimensional census rows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)

/-- The natural permutation representation on the pair set, pulled back to
the original group through the literal top map. -/
def pulledBackCoordinateTopAction :
    Representation (ZMod 2) U (I → ZMod 2) :=
  (permutationFunctionRepresentation (ZMod 2) F.top.range I).comp F.top.rangeRestrict

/-- Pair-constant functions form an equivariant copy of the pulled-back
pair permutation module. -/
def pairConstantIntertwiner :
    F.pulledBackCoordinateTopAction.IntertwiningMap
      (permutationFunctionRepresentation (ZMod 2) U X) where
  toLinearMap := F.pairConstant
  isIntertwining' u := by
    apply LinearMap.ext
    intro a
    simpa only [LinearMap.comp_apply] using (F.pairConstant_action u a).symm

theorem pairConstantIntertwiner_injective :
    Function.Injective F.pairConstantIntertwiner :=
  F.pairConstant_injective

/-- Pair-sum is equivariant for the original point action and the pulled
back top action. -/
def pairSumIntertwiner :
    (permutationFunctionRepresentation (ZMod 2) U X).IntertwiningMap
      F.pulledBackCoordinateTopAction where
  toLinearMap := F.pairSum
  isIntertwining' u := by
    apply LinearMap.ext
    intro f
    funext i
    change f ((((u⁻¹ : U) : Equiv.Perm X) (F.frame (i, 0)))) +
        f ((((u⁻¹ : U) : Equiv.Perm X) (F.frame (i, 1)))) =
      f (F.frame ((F.top u)⁻¹ i, 0)) +
        f (F.frame ((F.top u)⁻¹ i, 1))
    rw [F.action_frame, F.action_frame, map_inv]
    have hsum (b : ZMod 2) :
        f (F.frame (F.top u⁻¹ i, 0 + b)) +
            f (F.frame (F.top u⁻¹ i, 1 + b)) =
          f (F.frame (F.top u⁻¹ i, 0)) +
            f (F.frame (F.top u⁻¹ i, 1)) := by
      fin_cases b <;> simp [add_comm]
    simpa only [map_inv] using hsum (F.offset u⁻¹ i)

/-- A linear right inverse to pair-sum, obtained by putting the requested
coordinate on the zero point of each pair. -/
def pairSumSection : (I → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2) where
  toFun a x :=
    if (F.frame.symm x).2 = 0 then a (F.frame.symm x).1 else 0
  map_add' a b := by
    funext x
    by_cases h : (F.frame.symm x).2 = 0 <;> simp [h]
  map_smul' c a := by
    funext x
    by_cases h : (F.frame.symm x).2 = 0 <;> simp [h]

@[simp] theorem pairSumSection_frame
    (a : I → ZMod 2) (i : I) (b : ZMod 2) :
    F.pairSumSection a (F.frame (i, b)) = if b = 0 then a i else 0 := by
  change (if (F.frame.symm (F.frame (i, b))).2 = 0 then
    a (F.frame.symm (F.frame (i, b))).1 else 0) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem pairSum_pairSumSection (a : I → ZMod 2) :
    F.pairSum (F.pairSumSection a) = a := by
  funext i
  change F.pairSumSection a (F.frame (i, 0)) +
      F.pairSumSection a (F.frame (i, 1)) = a i
  simp [F.pairSumSection_frame]

theorem pairSumIntertwiner_surjective :
    Function.Surjective F.pairSumIntertwiner := by
  intro a
  exact ⟨F.pairSumSection a, F.pairSum_pairSumSection a⟩

/-- A subrepresentation of the pair module pulled back to the original
group descends to the intrinsic top range because `rangeRestrict` is onto. -/
def descendPulledBackSubrepresentation
    (M : Subrepresentation F.pulledBackCoordinateTopAction) :
    Subrepresentation (permutationFunctionRepresentation (ZMod 2) F.top.range I) where
  toSubmodule := M.toSubmodule
  apply_mem_toSubmodule t v hv := by
    obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
    exact M.apply_mem_toSubmodule u hv

/-- The pair-constant inclusion and pair-sum quotient are exact in the
literal point coordinates. -/
theorem pairConstant_pairSum_exact :
    LinearMap.range
        (Representation.IntertwiningMap.equivLinearMapAsModule
          F.pulledBackCoordinateTopAction
          (permutationFunctionRepresentation (ZMod 2) U X)
          F.pairConstantIntertwiner) =
      LinearMap.ker
        (Representation.IntertwiningMap.equivLinearMapAsModule
          (permutationFunctionRepresentation (ZMod 2) U X)
          F.pulledBackCoordinateTopAction F.pairSumIntertwiner) := by
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    exact F.pairSum_pairConstant a
  · intro hf
    have hsum : F.pairSum f = 0 := hf
    have hdelta : f ∈ F.pairDelta.ker := by
      change F.pairConstant (F.pairSum f) = 0
      rw [hsum, map_zero]
    rw [F.pairDelta_ker] at hdelta
    exact hdelta

/-- Ground-field form of the same exact sequence, for constructions of
subrepresentation quotients before passing to group-algebra modules. -/
theorem pairConstant_pairSum_exact_linear :
    LinearMap.range F.pairConstantIntertwiner.toLinearMap =
      LinearMap.ker F.pairSumIntertwiner.toLinearMap := by
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    exact F.pairSum_pairConstant a
  · intro hf
    have hsum : F.pairSum f = 0 := hf
    have hdelta : f ∈ F.pairDelta.ker := by
      change F.pairConstant (F.pairSum f) = 0
      rw [hsum, map_zero]
    rw [F.pairDelta_ker] at hdelta
    exact hdelta

/-- A uniform `H`-generator theorem on the pulled-back pair module gives a
uniform `2H`-generator theorem on the full point permutation module. -/
theorem permutationFunctionRepresentation_uniform_of_pairTop
    (H : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      F.pulledBackCoordinateTopAction H) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) (H + H) :=
  UniformSubrepresentationGeneratorBound.of_exact
    F.pulledBackCoordinateTopAction
    (permutationFunctionRepresentation (ZMod 2) U X)
    F.pulledBackCoordinateTopAction
    F.pairConstantIntertwiner F.pairSumIntertwiner
    F.pairConstantIntertwiner_injective F.pairConstant_pairSum_exact
    huniform huniform

/-- Version stated on the intrinsic top-range representation.  Surjectivity
of `rangeRestrict` identifies its pullback with the pair-module action used
in the exact sequence. -/
theorem permutationFunctionRepresentation_uniform_of_coordinateTop
    (H : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range I) H) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) (H + H) :=
  F.permutationFunctionRepresentation_uniform_of_pairTop H
    (UniformSubrepresentationGeneratorBound.comp_of_surjective
      (permutationFunctionRepresentation (ZMod 2) F.top.range I) F.top.rangeRestrict
      F.top.rangeRestrict_surjective huniform)

/-- The dual full point module has the same doubled uniform bound. -/
theorem permutationFunctionRepresentation_dual_uniform_of_pairTop
    [Finite X]
    (H : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      F.pulledBackCoordinateTopAction H) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X).dual (H + H) :=
  permutationFunctionRepresentation_dual_uniform
    (F.permutationFunctionRepresentation_uniform_of_pairTop H huniform)

/-- Dual full-module version from a theorem on the intrinsic pair top. -/
theorem permutationFunctionRepresentation_dual_uniform_of_coordinateTop
    [Finite X]
    (H : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range I) H) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X).dual (H + H) :=
  permutationFunctionRepresentation_dual_uniform
    (F.permutationFunctionRepresentation_uniform_of_coordinateTop H huniform)

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
