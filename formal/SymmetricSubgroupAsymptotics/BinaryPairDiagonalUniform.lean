import SymmetricSubgroupAsymptotics.BinaryPairFrameEquivariance
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! Pair-constant functions embed in the original point permutation module.
Thus an original natural uniform generator bound also bounds the actual
pair-image module. The original extension may have arbitrary offsets and
correlated flips; no complement or cycle on the pair set is required. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

def pairDiagonalInclusion :
    Representation.IntertwiningMap (A := ZMod 2) (V := I → ZMod 2) (W := X → ZMod 2)
      ((permutationFunctionRepresentation (ZMod 2) F.top.range I).comp F.top.rangeRestrict)
      (permutationFunctionRepresentation (ZMod 2) U X) where
  toLinearMap := LinearMap.pi fun x ↦
    (LinearMap.proj (F.frame.symm x).1 : (I → ZMod 2) →ₗ[ZMod 2] ZMod 2)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    funext x
    change v ((F.top g)⁻¹ (F.frame.symm x).1) =
      v (F.frame.symm ((g : Equiv.Perm X)⁻¹ x)).1
    have h := F.intertwine g⁻¹ (F.frame.symm x)
    simpa only [F.frame.apply_symm_apply, map_inv, Subgroup.coe_inv] using
      (congrArg v h).symm

theorem pairDiagonalInclusion_injective : Function.Injective F.pairDiagonalInclusion := by
  intro v w h
  funext i
  have hi := congrFun h (F.frame (i, 0))
  change v (F.frame.symm (F.frame (i, 0))).1 =
    w (F.frame.symm (F.frame (i, 0))).1 at hi
  simpa only [F.frame.symm_apply_apply] using hi

theorem uniform_pair_action_of_original (t : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) t) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range I) t := by
  apply UniformSubrepresentationGeneratorBound.of_comp
    (permutationFunctionRepresentation (ZMod 2) F.top.range I) F.top.rangeRestrict
  exact huniform.of_injective F.pairDiagonalInclusion F.pairDiagonalInclusion_injective

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
