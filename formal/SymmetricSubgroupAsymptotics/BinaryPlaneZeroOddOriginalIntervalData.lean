import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalNonbinarySocles
import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalBinaryQuotient
import SymmetricSubgroupAsymptotics.FaithfulPermutationOfCardBound
import SymmetricSubgroupAsymptotics.SocleGeneratorCharacterInterval

/-! Complete original normal interval for zero-odd/no-pair quartets.
The normal closure of an ACTUAL cubic subgroup is retained; its same
original quotient has faithful padded regular action on eight points. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalIntervalData
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneLineFramePairing (Affine Point)
open OriginalKernelModuleChart

def data (U : Subgroup (Equiv.Perm (Fin 16)))
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
    (hj : Function.Injective j) : SocleGeneratorCharacterIntervalData U := by
  letI : Finite A := Finite.of_injective j hj
  have hinj := BinaryPlaneZeroOddOriginalGeometry.top_injective U C rho pi hlinear
    pointChart hpoint hzero heven hNoPair
  let hex := BinaryPlaneFaithfulOriginalOrder.exists_single_cubic_order C hinj heven pi hpi A E
  let k := Classical.choose hex
  have hG := Classical.choose_spec hex
  let hp := BinaryPlaneFaithfulOriginalOrder.exists_actual_cubic_subgroup k hG
  let P := Classical.choose hp
  have hP := Classical.choose_spec hp
  let D := SingleCubicBinaryResidual.retained P
  letI : D.Normal := SingleCubicBinaryResidual.retained_normal P
  have hbinary : IsPGroup 2 (U ⧸ D) := SingleCubicBinaryResidual.binary_quotient P hP k hG
  have hcard : Nat.card (U ⧸ D)≤8 :=
    BinaryPlaneZeroOddOriginalBinaryQuotient.quotient_card_le_eight U C rho pi hpi hlinear
      pointChart hpoint hzero heven hNoPair A E j hj D hbinary
  let hac := FaithfulPermutationOfCardBound.exists_action 8 hcard
  let action := Classical.choose hac
  have ha := Classical.choose_spec hac
  exact {
    E := D
    quotientDegree := 8
    quotientAction := action
    quotientAction_injective := ha
    slots := 2
    quotientSocleGenerators := by
      intro N hnot
      letI := N.property
      have hn : ¬ IsPGroup 2 (U ⧸ N.val) := by
        intro hb
        exact hnot ((SingleCubicBinaryResidual.binary_iff_retained_le P hP k hG N.val).mp hb)
      exact BinaryPlaneZeroOddOriginalNonbinarySocles.socle_bound U C rho pi hpi hlinear
        pointChart hpoint hzero heven hNoPair A E j hj N.val hn }

end SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalIntervalData
