import SymmetricSubgroupAsymptotics.SixPairFullKernelCenterBits

/-! Original conjugation on the actual center is the physical three-label
permutation representation. This retains the same denominator for later
invariant-subquotient bounds. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairFullKernelCenterBits
open SixPairCoarseCenterTransport

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

/-- No unrelated action is chosen on the original center. -/
theorem bits_conjugate
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
    (g : U) (z : SixPairFullKernelCenter.centerImage F E) (j : Fin 3) :
    bits F E (MulAut.conjNormal g z) j=
      bits F E z (((SixPairNestedTopFrames.nestedFrame F E).top g)⁻¹ j) := by
  have hs := hasBits_conjugate F E g (kernel F E z) (bits F E z)
    (hasBits F E hfull z)
  have he : kernel F E (MulAut.conjNormal g z)=
      MulAut.conjNormal g (kernel F E z) := by
    apply Subtype.ext
    rfl
  change (((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j
    (kernel F E (MulAut.conjNormal g z))) (0,0)).2=_
  rw [he,hs j 0 0]
  exact zero_add _

end SymmetricSubgroupAsymptotics.SixPairFullKernelCenterBits
