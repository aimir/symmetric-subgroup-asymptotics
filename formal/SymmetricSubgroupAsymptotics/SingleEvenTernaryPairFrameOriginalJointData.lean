import SymmetricSubgroupAsymptotics.SingleEvenTernarySixImage
import SymmetricSubgroupAsymptotics.BinaryKernelSingleEvenTopOriginalQuotientSocles
import SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6
import SymmetricSubgroupAsymptotics.OriginalKernelNonbinaryResidual
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SingleEvenTernaryPairFrameOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem quotientSocle {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) (hle : F.top.range≤SingleEvenTernarySixImage.action.range)
    (hpair : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 2 := by
  let E := SixPairPrimitiveAllNormalB6.originalKernelChart F
  let A := SixPairPrimitiveAllNormalB6.kernelModule F
  letI : FiniteDimensional (ZMod 2) A := by
    change FiniteDimensional (ZMod 2) F.kernelSpace
    infer_instance
  let pi := F.top.rangeRestrict
  let j : Representation.IntertwiningMap A.ρ
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) :=
    { toLinearMap := F.kernelSpace.subtype, isIntertwining' _ := rfl }
  have hu : UniformSubrepresentationGeneratorBound A.ρ 1 :=
    hpair.of_injective j (fun _ _ h => Subtype.ext h)
  have htwo : IsPGroup 2 pi.ker := E.kernel_isPGroup_two pi A
  letI : IsSolvable F.top.range := SingleEvenTernarySixImage.isSolvable F.top.range hle
  letI : Group.IsNilpotent pi.ker := htwo.isNilpotent
  letI : IsSolvable U := solvable_of_ker_le_range pi.ker.subtype pi
    (by rw [Subgroup.range_subtype])
  have hc : Nat.card F.top.range∣3^2*2 := by
    simpa using SingleEvenTernarySixImage.subgroup_card F.top.range hle
  exact BinaryKernelSingleEvenTopOriginalQuotientSocles.quotientSocle pi
    F.top.rangeRestrict_surjective A E hu 2 hc
    (SixPointTernaryAxesNormalGenerators.normal_generating_pairs F.top.range
      (hle.trans SingleEvenTernarySixImage.range_le)) N

def jointData (T : DegreeTwoPairTopFiniteInterface 12)
    (F : BinaryPairFrame T.top (Fin 6)) (hle : F.top.range≤SingleEvenTernarySixImage.action.range)
    (hpair : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1)
    (hnatural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T.top (Fin 12)) 2) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData T 2 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    T.normalRegistry (fun N => by
      letI := N.2
      exact quotientSocle F hle hpair N.1)
  natural := hnatural
end SymmetricSubgroupAsymptotics.SingleEvenTernaryPairFrameOriginalJointData
