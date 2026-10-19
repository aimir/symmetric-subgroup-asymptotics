import SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingNonzeroOddIntervalData
import SymmetricSubgroupAsymptotics.SixteenPointSemanticEightComparatorNumerics

/-! Final original-weight source of an actual affine nonzero-odd quartet kernel chart.
All structural interval and numerical source obligations are constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingNonzeroOddActualSource
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open Non2UnipotentPrefixFiniteMenu
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneWreathActualOddKernel

def source (i : PreE7NonPairActionClass 16)
    (C : Subgroup Frame)
    (hO : oddKernel C≠⊥)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (pi : preE7NonPairAction 16 i →* C) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) C) [FiniteDimensional (ZMod 2) A]
    (E : OriginalKernelModuleChart pi A)
    (j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C))
    (hj : Function.Injective j)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7RankTailSourceOrYonedaTopData 16 i :=
  SixteenPointSemanticEightComparatorNumerics.source hMN hZmud lit family
    (SixteenPointSemanticAlternatingNonzeroOddIntervalData.data (preE7NonPairAction 16 i)
      C hO heven pi hpi A E j hj) rfl rfl

end SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingNonzeroOddActualSource
