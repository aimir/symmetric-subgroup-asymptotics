import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignBottomWreathEpi
import SymmetricSubgroupAsymptotics.SemidirectBinaryKernelCentralAxis

/-!
# Binary central series above the rank-two bottom wreath quotient

The kernel of the bottom-to-wreath epimorphism lies in the chosen binary
Schur complement.  A central order-two axis in that top kernel acts
trivially on the ternary plane, hence is central in the whole original
group.  This gives the same two-step central recursion used for every
proper section.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private abbrev G (w : ℕ) (U : PreE7NonPairActionClass w) :=
  preE7NonPairAction w U

/-- The chosen bottom complement is a finite 2-group. -/
theorem degreeThreeFourBlockTwoSignBottomComplement_isPGroup
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    IsPGroup 2
      (degreeThreeFourBlockTwoSignBottomComplement
        block P hr hs hcomponent hbinary) :=
  (degreeThreeFourBlock_signedQuotient_isPGroup
      block P hr hs hcomponent hbinary).of_equiv
    (degreeThreeFourBlockTwoSignBottomComplementTopEquiv
      block P
      (degreeThreeFourBlockTwoSignBottomComplement
        block P hr hs hcomponent hbinary)
      (degreeThreeFourBlockTwoSignBottomComplement_isComplement
        block P hr hs hcomponent hbinary)).symm

/-- The kernel left in the chosen bottom complement has order at most
four. -/
theorem degreeThreeFourBlockTwoSignBottomComplementD8Map_kernel_card_le_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Nat.card (degreeThreeFourBlockTwoSignBottomComplementD8Map
      block P hr hs hcomponent hbinary htwo hfin).ker ≤ 4 := by
  let H := degreeThreeFourBlockTwoSignBottomComplement
    block P hr hs hcomponent hbinary
  let f := degreeThreeFourBlockTwoSignBottomComplementD8Map
    block P hr hs hcomponent hbinary htwo hfin
  let e := degreeThreeFourBlockTwoSignBottomComplementTopEquiv
    block P H
      (degreeThreeFourBlockTwoSignBottomComplement_isComplement
        block P hr hs hcomponent hbinary)
  have hH : Nat.card H ≤ 32 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 32
    rcases degreeThreeFourBlockTwoSign_signedQuotient_card_cases
      block P hr hs hcomponent hbinary htwo with h16 | h32
    · omega
    · omega
  have hfactor := f.ker.card_mul_index
  have hindex : f.ker.index = 8 := by
    rw [Subgroup.index_ker,
      f.range_eq_top_of_surjective
        (degreeThreeFourBlockTwoSignBottomComplementD8Map_surjective
          block P hr hs hcomponent hbinary htwo hfin),
      Nat.card_congr Subgroup.topEquiv.toEquiv]
    rw [SemidirectProduct.card, Nat.card_prod]
    norm_num [Nat.card_zmod]
  rw [hindex] at hfactor
  change Nat.card f.ker * 8 = Nat.card H at hfactor
  change Nat.card f.ker ≤ 4
  omega

/-- Central order-two axis in the split bottom map. -/
noncomputable def degreeThreeFourBlockTwoSignBottomSemidirectCentralAxis
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2)
    (hkernel_ne :
      (degreeThreeFourBlockTwoSignBottomComplementD8Map
        block P hr hs hcomponent hbinary htwo hfin).ker ≠ ⊥) :
    CentralOrderTwoKernelAxis
      (degreeThreeFourBlockTwoSignBottomSemidirectMap
        block P hr hs hcomponent hbinary htwo hfin) :=
  SemidirectBinaryKernelCentralAxis.ofTopKernel
    (degreeThreeFourBlockTwoSignBottomKernelTernaryEquiv
      block P hr hs hcomponent hbinary htwo hfin)
    (degreeThreeFourBlockTwoSignBottomComplementD8Map
      block P hr hs hcomponent hbinary htwo hfin)
    (degreeThreeFourBlockTwoSignBottomSemidirect_compatible
      block P hr hs hcomponent hbinary htwo hfin)
    (degreeThreeFourBlockTwoSignBottomComplement_isPGroup
      block P hr hs hcomponent hbinary)
    hkernel_ne
    (degreeThreeFourBlockTwoSignBottomComplementD8Map_kernel_card_le_four
      block P hr hs hcomponent hbinary htwo hfin)

/-- The split bottom axis after postcomposing with the canonical wreath
equivalence. -/
noncomputable def degreeThreeFourBlockTwoSignBottomSplitWreathCentralAxis
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2)
    (hkernel_ne :
      (degreeThreeFourBlockTwoSignBottomComplementD8Map
        block P hr hs hcomponent hbinary htwo hfin).ker ≠ ⊥) :
    CentralOrderTwoKernelAxis
      (DegreeSixS3Wreath.semidirectEquiv.symm.toMonoidHom.comp
        (degreeThreeFourBlockTwoSignBottomSemidirectMap
          block P hr hs hcomponent hbinary htwo hfin)) :=
  (degreeThreeFourBlockTwoSignBottomSemidirectCentralAxis
    block P hr hs hcomponent hbinary htwo hfin hkernel_ne).postcomp
      DegreeSixS3Wreath.semidirectEquiv.symm.toMonoidHom
      DegreeSixS3Wreath.semidirectEquiv.symm.injective

/-- The literal bottom wreath map agrees with the split map through the
chosen Schur-complement equivalence. -/
theorem degreeThreeFourBlockTwoSignBottomWreathMap_comp_semidirectEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    let H := degreeThreeFourBlockTwoSignBottomComplement
      block P hr hs hcomponent hbinary
    let e := degreeThreeFourBlockTwoSignBottomSemidirectEquiv
      block P H
        (degreeThreeFourBlockTwoSignBottomComplement_isComplement
          block P hr hs hcomponent hbinary)
    (degreeThreeFourBlockTwoSignBottomWreathMap
        block P hr hs hcomponent hbinary htwo hfin).comp e.toMonoidHom =
      DegreeSixS3Wreath.semidirectEquiv.symm.toMonoidHom.comp
        (degreeThreeFourBlockTwoSignBottomSemidirectMap
          block P hr hs hcomponent hbinary htwo hfin) := by
  dsimp only
  apply MonoidHom.ext
  intro x
  simp [degreeThreeFourBlockTwoSignBottomWreathMap]

/-- If the chosen complement has no residual binary kernel, the bottom
wreath epimorphism is an isomorphism. -/
theorem degreeThreeFourBlockTwoSignBottomWreathMap_injective_of_topKernel_eq_bot
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2)
    (hkernel :
      (degreeThreeFourBlockTwoSignBottomComplementD8Map
        block P hr hs hcomponent hbinary htwo hfin).ker = ⊥) :
    Function.Injective
      (degreeThreeFourBlockTwoSignBottomWreathMap
        block P hr hs hcomponent hbinary htwo hfin) := by
  let H := degreeThreeFourBlockTwoSignBottomComplement
    block P hr hs hcomponent hbinary
  let e := degreeThreeFourBlockTwoSignBottomSemidirectEquiv
    block P H
      (degreeThreeFourBlockTwoSignBottomComplement_isComplement
        block P hr hs hcomponent hbinary)
  have htop : Function.Injective
      (degreeThreeFourBlockTwoSignBottomComplementD8Map
        block P hr hs hcomponent hbinary htwo hfin) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hkernel
  have hsplit : Function.Injective
      (degreeThreeFourBlockTwoSignBottomSemidirectMap
        block P hr hs hcomponent hbinary htwo hfin) :=
    SemidirectBinaryKernelCentralAxis.map_injective
      (degreeThreeFourBlockTwoSignBottomKernelTernaryEquiv
        block P hr hs hcomponent hbinary htwo hfin).toMonoidHom
      (degreeThreeFourBlockTwoSignBottomComplementD8Map
        block P hr hs hcomponent hbinary htwo hfin)
      (degreeThreeFourBlockTwoSignBottomSemidirect_compatible
        block P hr hs hcomponent hbinary htwo hfin)
      (degreeThreeFourBlockTwoSignBottomKernelTernaryEquiv
        block P hr hs hcomponent hbinary htwo hfin).injective
      htop
  intro x y hxy
  apply e.symm.injective
  apply hsplit
  apply DegreeSixS3Wreath.semidirectEquiv.symm.injective
  simpa only [degreeThreeFourBlockTwoSignBottomWreathMap,
    MonoidHom.comp_apply, MulEquiv.apply_symm_apply] using hxy

/-- Central order-two axis transported back to the original group. -/
noncomputable def degreeThreeFourBlockTwoSignBottomWreathCentralAxis
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2)
    (hkernel_ne :
      (degreeThreeFourBlockTwoSignBottomComplementD8Map
        block P hr hs hcomponent hbinary htwo hfin).ker ≠ ⊥) :
    CentralOrderTwoKernelAxis
      (degreeThreeFourBlockTwoSignBottomWreathMap
        block P hr hs hcomponent hbinary htwo hfin) := by
  let H := degreeThreeFourBlockTwoSignBottomComplement
    block P hr hs hcomponent hbinary
  let e := degreeThreeFourBlockTwoSignBottomSemidirectEquiv
    block P H
      (degreeThreeFourBlockTwoSignBottomComplement_isComplement
        block P hr hs hcomponent hbinary)
  exact
    (degreeThreeFourBlockTwoSignBottomSplitWreathCentralAxis
      block P hr hs hcomponent hbinary htwo hfin hkernel_ne).mapDomainEquiv
        e
        (degreeThreeFourBlockTwoSignBottomWreathMap
          block P hr hs hcomponent hbinary htwo hfin)
        (degreeThreeFourBlockTwoSignBottomWreathMap_comp_semidirectEquiv
          block P hr hs hcomponent hbinary htwo hfin)

/-- The nontrivial bottom kernel has the two-step central series required
by the recursive `QStar` comparison. -/
noncomputable def degreeThreeFourBlockTwoSignBottomWreathKernelCentralSeries
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2)
    (hkernel_ne :
      (degreeThreeFourBlockTwoSignBottomComplementD8Map
        block P hr hs hcomponent hbinary htwo hfin).ker ≠ ⊥) :
    BinaryNormalKernelCentralSeries (G w U)
      (degreeThreeFourBlockTwoSignBottomWreathMap
        block P hr hs hcomponent hbinary htwo hfin).ker :=
  (degreeThreeFourBlockTwoSignBottomWreathCentralAxis
    block P hr hs hcomponent hbinary htwo hfin hkernel_ne).toCentralSeries
      (degreeThreeFourBlockTwoSignBottomWreathMap_kernel_card_le_four
        block P hr hs hcomponent hbinary htwo hfin)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
