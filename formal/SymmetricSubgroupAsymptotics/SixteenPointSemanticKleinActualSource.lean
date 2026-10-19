import SymmetricSubgroupAsymptotics.SixteenPointSemanticKleinIntervalData
import SymmetricSubgroupAsymptotics.SixteenPointSemanticEightComparatorNumerics

/-! Final original-weight source of an actual affine V4 kernel chart.
All structural interval and numerical source obligations are constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticKleinActualSource
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open Non2UnipotentPrefixFiniteMenu
abbrev R := BinaryRegularKleinWreath.R
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

def source (i : PreE7NonPairActionClass 16)
    (C : Subgroup (W (R := R) (I := R)))
    (pi : preE7NonPairAction 16 i →* C) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) C) [FiniteDimensional (ZMod 2) A]
    (E : OriginalKernelModuleChart pi A)
    (j : Representation.IntertwiningMap A.ρ (BinaryPlaneKleinUniform.representation C))
    (hj : Function.Injective j)
    (hblocks : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := R) →* R).comp C.subtype))
    (hU : ¬ IsPGroup 2 (preE7NonPairAction 16 i))
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7RankTailSourceOrYonedaTopData 16 i :=
  SixteenPointSemanticEightComparatorNumerics.source hMN hZmud lit family
    (SixteenPointSemanticKleinIntervalData.data (preE7NonPairAction 16 i)
      C pi hpi A E j hj hblocks hU) rfl rfl

end SymmetricSubgroupAsymptotics.SixteenPointSemanticKleinActualSource
