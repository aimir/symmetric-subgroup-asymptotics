import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalUniform
import SymmetricSubgroupAsymptotics.OriginalKernelSectionUniform
import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

/-! The entire original quotient socle is bounded in the branch where
it lies in the literal retained translation kernel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalInsideSocle
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
    (hinside : finiteGroupSocle (U ⧸ N)≤(base pi N).ker) :
    SocleNormalGeneratorBound (U ⧸ N) 2 := by
  letI : Finite A := Finite.of_injective j hj
  letI : FiniteDimensional (ZMod 2) (E.sectionRepresentation pi A N) := by
    change FiniteDimensional (ZMod 2) (E.sectionModule pi A N)
    infer_instance
  let hu := BinaryPlaneZeroOddOriginalUniform.uniform U C rho pi hlinear pointChart hpoint
    hzero heven hNoPair
  have hA : UniformSubrepresentationGeneratorBound A.ρ 2 := hu.of_injective j hj
  have hs := E.sectionUniform pi A N hpi hA
  have hn : MarkedC4.normalGen (finiteGroupSocle (U ⧸ N))≤2 :=
    (E.quotientChart pi A N).kernel_normalGen_le (base pi N)
      (E.sectionRepresentation pi A N) (base_surjective pi N) 2 hs _ hinside
  exact (socleNormalGeneratorBound_iff_normalGen_le (U ⧸ N) 2).mpr hn

end SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalInsideSocle
