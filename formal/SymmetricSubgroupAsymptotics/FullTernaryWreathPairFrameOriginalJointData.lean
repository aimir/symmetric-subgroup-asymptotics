import SymmetricSubgroupAsymptotics.TernaryLocalWreathSixFaithful
import SymmetricSubgroupAsymptotics.BinaryKernelProperTopRelativeHeads
import SymmetricSubgroupAsymptotics.BinaryPairUniformOriginalKernelHead
import SymmetricSubgroupAsymptotics.BinaryKernelSchurOriginalQuotientSocles
import SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FullTernaryWreathPairFrameOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open SixPairLocalWreathSocles (Model literalAction regularRotation regularReflection)

theorem quotientSocle {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) (himage : F.top.range=literalAction.range)
    {C D : Type} [Group C] [Finite C] [IsCyclic C] [Group D] [Finite D] [IsCyclic D]
    (cover : C × D →* U ⧸ commutator U) (hcover : Function.Surjective cover)
    (hno : NoTernaryQuotient U) (N : Subgroup U) [N.Normal] :
    SocleNormalGeneratorBound (U ⧸ N) 2 := by
  letI : Finite SixPairLocalWreathSocles.Local := Finite.of_equiv
    (TernarySwapUpperNormalGenerators.Ternary × TernarySwapUpperNormalGenerators.Binary)
    SemidirectProduct.equivProd.symm
  letI : Finite Model := Finite.of_equiv
    ((SixPairLocalWreathSocles.Local × SixPairLocalWreathSocles.Local) ×
      TernarySwapUpperNormalGenerators.Binary) SemidirectProduct.equivProd.symm
  let E := SixPairPrimitiveAllNormalB6.originalKernelChart F
  let A := SixPairPrimitiveAllNormalB6.kernelModule F
  letI : FiniteDimensional (ZMod 2) A := by
    change FiniteDimensional (ZMod 2) F.kernelSpace
    infer_instance
  let pi := F.top.rangeRestrict
  let e : F.top.range ≃* Model :=
    (MulEquiv.subgroupCongr himage).trans TernaryLocalWreathSixFaithful.canonicalEquiv.symm
  let c : F.top.range := ⟨literalAction regularRotation,by rw [himage]; exact ⟨_,rfl⟩⟩
  let b : F.top.range := ⟨literalAction regularReflection,by rw [himage]; exact ⟨_,rfl⟩⟩
  have hpair := BinarySixPointSymmetricMatrixBlocks.uniform_subgroup F.top.range c b
    SixPairLocalWreathSocles.regularRotation_action SixPairLocalWreathSocles.regularReflection_action
  have hsame : pi.ker=F.top.ker := by
    ext u
    change F.top.rangeRestrict u=1 ↔ F.top u=1
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  have hkernel : ∀ (L : Subgroup U) [L.Normal],L≤pi.ker →
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L)≤1 := by
    intro L _ hL
    exact BinaryPairUniformOriginalKernelHead.normal_kernel_head_le_one F hpair L (hsame ▸ hL)
  have htwo : IsPGroup 2 pi.ker := E.kernel_isPGroup_two pi A
  have hK : IsMulCommutative pi.ker := isMulCommutative_iff.mpr
    (fun x y => E.equiv.symm.injective (by rw [map_mul,map_mul,mul_comm]))
  letI : IsSolvable Model := TernaryLocalWreathProperRelativeHead.isSolvable
  letI : IsSolvable F.top.range := solvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  letI : Group.IsNilpotent pi.ker := htwo.isNilpotent
  letI : IsSolvable U := solvable_of_ker_le_range pi.ker.subtype pi
    (by rw [Subgroup.range_subtype])
  have hhead := BinaryKernelProperTopRelativeHeads.relative_head_le_two
    (TernaryLocalWreathSixFaithful.proper_head e)
    pi F.top.rangeRestrict_surjective hK hkernel cover hcover
  exact BinaryKernelSchurOriginalQuotientSocles.quotientSocle
    (by simp : Nat.card (Fin 12)=12) pi F.top.rangeRestrict_surjective A E
    (fun L _ => CoprimeKernelQuotientSocles.normalGen_image_bound e.symm.toMonoidHom
      e.symm.surjective 2 (fun M hM => by
        letI := hM
        exact TernaryLocalWreathNormalGenerators.normalGen_le M) L)
    hno hhead N

def jointData (T : DegreeTwoPairTopFiniteInterface 12)
    (F : BinaryPairFrame T.top (Fin 6)) (himage : F.top.range=literalAction.range)
    {C D : Type} [Group C] [Finite C] [IsCyclic C] [Group D] [Finite D] [IsCyclic D]
    (cover : C × D →* T.top ⧸ commutator T.top) (hcover : Function.Surjective cover)
    (hno : NoTernaryQuotient T.top)
    (hnatural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T.top (Fin 12)) 2) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData T 2 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    T.normalRegistry (fun N => by
      letI := N.2
      exact quotientSocle F himage cover hcover hno N.1)
  natural := hnatural
end SymmetricSubgroupAsymptotics.FullTernaryWreathPairFrameOriginalJointData
