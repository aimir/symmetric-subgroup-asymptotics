import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! Functions constant on the physical fibres embed equivariantly in the
original natural module. The actual quotient top retains every correlation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame

variable {k X I F : Type} [Field k] {U : Subgroup (Equiv.Perm X)}
    (C : ProductBlockFrame U I F)

def diagonalInclusion :
    Representation.IntertwiningMap (A := k) (V := I → k) (W := X → k)
      ((permutationFunctionRepresentation k C.top.range I).comp C.top.rangeRestrict)
      (permutationFunctionRepresentation k U X) where
  toLinearMap := LinearMap.pi fun x =>
    (LinearMap.proj (C.frame.symm x).1 : (I → k) →ₗ[k] k)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    funext x
    change v ((C.top g)⁻¹ (C.frame.symm x).1) =
      v (C.frame.symm ((g : Equiv.Perm X)⁻¹ x)).1
    have h := C.intertwine g⁻¹ (C.frame.symm x)
    simpa only [C.frame.apply_symm_apply,map_inv,Subgroup.coe_inv] using
      (congrArg v h).symm

theorem diagonalInclusion_injective [Nonempty F] :
    Function.Injective (C.diagonalInclusion (k := k)) := by
  intro v w h
  funext i
  let f : F := Classical.choice inferInstance
  have hi := congrFun h (C.frame (i,f))
  change v (C.frame.symm (C.frame (i,f))).1 =
    w (C.frame.symm (C.frame (i,f))).1 at hi
  simpa only [C.frame.symm_apply_apply] using hi

theorem uniform_top_action_of_original [Nonempty F] (t : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k U X) t) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k C.top.range I) t := by
  apply UniformSubrepresentationGeneratorBound.of_comp
    (permutationFunctionRepresentation k C.top.range I) C.top.rangeRestrict
  exact huniform.of_injective C.diagonalInclusion C.diagonalInclusion_injective

end SymmetricSubgroupAsymptotics.ProductBlockFrame
