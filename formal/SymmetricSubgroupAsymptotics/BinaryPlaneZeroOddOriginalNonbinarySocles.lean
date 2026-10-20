import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalOutsideSocle
import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalInsideSocle
import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulOriginalOddSocles

/-! The complete actual nonbinary original quotient socle bound in the
zero-odd/no-pair quartet branch. Odd and binary primary parts share the
same two positions by their actual coprime normal-generator maximum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalNonbinarySocles
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneLineFramePairing (Affine Point)
open OriginalKernelModuleChart

theorem socle_bound (U : Subgroup (Equiv.Perm (Fin 16)))
    (C : Subgroup Frame) (rho : U →* Affine) (pi : U →* C)
    (hpi : Function.Surjective pi)
    (hlinear : ∀ u : U, (rho u).right=(pi u : Frame))
    (pointChart : Point ≃ Fin 16)
    (hpoint : ∀ (u : U) p, pointChart (BinaryPlanePermutationWreathCoordinates.pointAction
      (rho u) p)=(u : Equiv.Perm (Fin 16)) (pointChart p))
    (hzero : oddKernel C=⊥)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (hNoPair : ¬ Nonempty (BinaryPairFrame U (Fin 8)))
    (A : Rep.{0} (ZMod 2) C) (E : OriginalKernelModuleChart pi A)
    (j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C))
    (hj : Function.Injective j) (N : Subgroup U) [N.Normal]
    (hnonbinary : ¬ IsPGroup 2 (U ⧸ N)) :
    SocleNormalGeneratorBound (U ⧸ N) 2 := by
  by_cases hi : finiteGroupSocle (U ⧸ N)≤(base pi N).ker
  · exact BinaryPlaneZeroOddOriginalInsideSocle.socle_bound U C rho pi hpi hlinear
      pointChart hpoint hzero heven hNoPair A E j hj N hi
  have hb := BinaryPlaneZeroOddOriginalOutsideSocle.binarySocle_bound U C rho pi hpi hlinear
    pointChart hpoint hzero heven hNoPair A E j hj N hnonbinary hi
  letI : Finite A := Finite.of_injective j hj
  have hinj := BinaryPlaneZeroOddOriginalGeometry.top_injective U C rho pi hlinear
    pointChart hpoint hzero heven hNoPair
  have ho := BinaryPlaneFaithfulOriginalOddSocles.normalGen_le_one C hinj heven pi hpi A E N
  apply (socleNormalGeneratorBound_iff_normalGen_le (U ⧸ N) 2).mpr
  exact (normalGen_finiteGroupSocle_le_max_primePrimaryParts 2 (U ⧸ N)).trans
    (max_le hb (ho.trans (by decide)))

end SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalNonbinarySocles
