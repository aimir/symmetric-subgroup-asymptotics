import SymmetricSubgroupAsymptotics.SixPairCoarseWreathHead

/-! Actual conjugation transports an original coarse-kernel restriction
between physical fibres. Both local changes of coordinates are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairLocalKernelConjugation
variable {X I J : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I) (E : ProductBlockFrame F.top.range J (ZMod 2))

 theorem coordinate_conjugate (g : U)
    (u : (SixPairNestedTopFrames.nestedFrame F E).top.ker) (i : J) :
    (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate i (MulAut.conjNormal g u)=
      (((SixPairNestedTopFrames.nestedFrame F E).wreathEmbedding g).left i)*
        ((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate
          (((SixPairNestedTopFrames.nestedFrame F E).top g)⁻¹ i) u)*
        ((((SixPairNestedTopFrames.nestedFrame F E).wreathEmbedding g).left i)⁻¹) := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  rw [←SixPairCoarseWreathHead.local_of_kernel F E]
  change (C.wreathEmbedding (g*u.val*g⁻¹)).left i=_
  have hu : C.top u.val=1 := u.property
  rw [map_mul,map_mul,map_inv]
  simp only [PermutationalWreathProduct.mul_left,PermutationalWreathProduct.mul_right,
    PermutationalWreathProduct.inv_left,Pi.mul_apply,Pi.inv_apply,
    ProductBlockFrame.wreathEmbedding_top,hu,mul_one,inv_one,
    Equiv.Perm.smul_def,Equiv.Perm.inv_def,Equiv.apply_symm_apply]
  rw [SixPairCoarseWreathHead.local_of_kernel F E]

end SymmetricSubgroupAsymptotics.SixPairLocalKernelConjugation
