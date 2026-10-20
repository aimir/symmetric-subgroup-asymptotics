import SymmetricSubgroupAsymptotics.QuarterTurnSixActualUpper
import SymmetricSubgroupAsymptotics.BinaryKernelOddCyclicTopRelativeHeads
import SymmetricSubgroupAsymptotics.BinaryPairUniformOriginalKernelHead
import SymmetricSubgroupAsymptotics.BinaryKernelSchurOriginalQuotientSocles
import SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuarterTurnPairFrameOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open SixPointTernaryQuarterTurnNormalGenerators (Model gen literalAction)

theorem quotientSocle {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) (hle : F.top.range≤literalAction.range)
    (lift : Model) (hlift : literalAction lift∈F.top.range) (hgen : lift.right=gen)
    (hpair : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1)
    (hno : NoTernaryQuotient U) (N : Subgroup U) [N.Normal] :
    SocleNormalGeneratorBound (U ⧸ N) 2 := by
  let E := SixPairPrimitiveAllNormalB6.originalKernelChart F
  let A := SixPairPrimitiveAllNormalB6.kernelModule F
  letI : FiniteDimensional (ZMod 2) A := by
    change FiniteDimensional (ZMod 2) F.kernelSpace
    infer_instance
  let pi := F.top.rangeRestrict
  let beta := QuarterTurnSixActualUpper.projection F.top.range hle
  have hb : Function.Surjective beta := QuarterTurnSixActualUpper.projection_surjective
    F.top.range hle ⟨literalAction lift,hlift⟩ lift rfl hgen
  have hodd : IsPGroup 3 beta.ker := QuarterTurnSixActualUpper.kernel_isPGroup F.top.range hle
  have hsame : pi.ker=F.top.ker := by
    ext u
    change F.top.rangeRestrict u=1 ↔ F.top u=1
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  have hkernel : ∀ (L : Subgroup U) [L.Normal],L≤pi.ker →
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L)≤1 := by
    intro L _ hL
    exact BinaryPairUniformOriginalKernelHead.normal_kernel_head_le_one F hpair L (hsame ▸ hL)
  have htwo : IsPGroup 2 pi.ker := E.kernel_isPGroup_two pi A
  letI : IsSolvable F.top.range := QuarterTurnSixActualUpper.isSolvable F.top.range hle
    ⟨literalAction lift,hlift⟩ lift rfl hgen
  letI : Group.IsNilpotent pi.ker := htwo.isNilpotent
  letI : IsSolvable U := solvable_of_ker_le_range pi.ker.subtype pi
    (by rw [Subgroup.range_subtype])
  have hhead := BinaryKernelOddCyclicTopRelativeHeads.relative_head_le_two pi
    F.top.rangeRestrict_surjective beta hb hodd hkernel
  exact BinaryKernelSchurOriginalQuotientSocles.quotientSocle
    (by simp : Nat.card (Fin 12)=12) pi F.top.rangeRestrict_surjective A E
    (fun L _ => SixPointTernaryQuarterTurnNormalGenerators.normalGen_le
      F.top.range hle lift hlift hgen L) hno hhead N

def jointData (T : DegreeTwoPairTopFiniteInterface 12)
    (F : BinaryPairFrame T.top (Fin 6)) (hle : F.top.range≤literalAction.range)
    (lift : Model) (hlift : literalAction lift∈F.top.range) (hgen : lift.right=gen)
    (hpair : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1)
    (hno : NoTernaryQuotient T.top)
    (hnatural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T.top (Fin 12)) 2) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData T 2 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    T.normalRegistry (fun N => by
      letI := N.2
      exact quotientSocle F hle lift hlift hgen hpair hno N.1)
  natural := hnatural
end SymmetricSubgroupAsymptotics.QuarterTurnPairFrameOriginalJointData
