import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalIntervalData
import SymmetricSubgroupAsymptotics.SixteenPointSemanticEightComparatorNumerics

/-! Final original-weight source constructor for the honest zero-odd,
no-binary-pair quartet branch. All original-N socle, retained comparator,
and numerical source obligations are constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingZeroOddActualSource
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneLineFramePairing (Affine Point)
open Non2UnipotentPrefixFiniteMenu

def source (i : PreE7NonPairActionClass 16) (C : Subgroup Frame)
    (rho : preE7NonPairAction 16 i →* Affine)
    (pi : preE7NonPairAction 16 i →* C) (hpi : Function.Surjective pi)
    (hlinear : ∀ u, (rho u).right=(pi u : Frame))
    (pointChart : Point ≃ Fin 16)
    (hpoint : ∀ (u : preE7NonPairAction 16 i) p,
      pointChart (BinaryPlanePermutationWreathCoordinates.pointAction (rho u) p)=
        (u : Equiv.Perm (Fin 16)) (pointChart p))
    (hzero : oddKernel C=⊥)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (hNoPair : ¬ Nonempty (BinaryPairFrame (preE7NonPairAction 16 i) (Fin 8)))
    (A : Rep.{0} (ZMod 2) C) (E : OriginalKernelModuleChart pi A)
    (j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C))
    (hj : Function.Injective j)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7RankTailSourceOrYonedaTopData 16 i :=
  SixteenPointSemanticEightComparatorNumerics.source hMN hZmud lit family
    (BinaryPlaneZeroOddOriginalIntervalData.data (preE7NonPairAction 16 i)
      C rho pi hpi hlinear pointChart hpoint hzero heven hNoPair A E j hj) rfl rfl

end SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingZeroOddActualSource
