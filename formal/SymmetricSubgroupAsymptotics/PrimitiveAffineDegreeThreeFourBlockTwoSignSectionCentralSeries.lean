import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionWreathEpi
import SymmetricSubgroupAsymptotics.SemidirectBinaryKernelCentralAxis

/-!
# Binary central series above the literal ternary section

The kernel of the section-to-wreath epimorphism lies entirely in the
chosen binary Schur complement.  A central order-two axis in that top
kernel acts trivially on the retained ternary plane, hence is central in
the whole section.  This supplies the central series required by the
generic `QStar` comparison without assuming that the section itself is a
2-group.
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

private abbrev G := preE7NonPairAction w U

/-- The chosen complement remains a finite 2-group. -/
theorem degreeThreeFourBlockTwoSignSectionComplement_isPGroup
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (N : TwoSignProperAxis (E block P)) :
    IsPGroup 2
      (degreeThreeFourBlockTwoSignSectionComplement
        block P hr hs hcomponent hbinary N) :=
  (degreeThreeFourBlockTwoSignSectionTop_isPGroup
      block P hr hs hcomponent hbinary N).of_equiv
    (degreeThreeFourBlockTwoSignSectionComplementTopEquiv
      block P N
      (degreeThreeFourBlockTwoSignSectionComplement
        block P hr hs hcomponent hbinary N)
      (degreeThreeFourBlockTwoSignSectionComplement_isComplement
        block P hr hs hcomponent hbinary N)).symm

/-- The kernel left in the chosen binary complement has order at most
four. -/
theorem degreeThreeFourBlockTwoSignSectionComplementD8Map_kernel_card_le_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Nat.card (degreeThreeFourBlockTwoSignSectionComplementD8Map
      block P hr hs hcomponent hbinary htwo N).ker ≤ 4 := by
  let H := degreeThreeFourBlockTwoSignSectionComplement
    block P hr hs hcomponent hbinary N
  let f := degreeThreeFourBlockTwoSignSectionComplementD8Map
    block P hr hs hcomponent hbinary htwo N
  let e := degreeThreeFourBlockTwoSignSectionComplementTopEquiv
    block P N H
      (degreeThreeFourBlockTwoSignSectionComplement_isComplement
        block P hr hs hcomponent hbinary N)
  have hH : Nat.card H ≤ 32 := by
    rw [Nat.card_congr e.toEquiv]
    exact degreeThreeFourBlockTwoSignSectionTop_card_le_thirty_two
      block P hr hs hcomponent hbinary htwo N
  have hfactor := f.ker.card_mul_index
  have hindex : f.ker.index = 8 := by
    rw [Subgroup.index_ker,
      f.range_eq_top_of_surjective
        (degreeThreeFourBlockTwoSignSectionComplementD8Map_surjective
          block P hr hs hcomponent hbinary htwo N),
      Nat.card_congr Subgroup.topEquiv.toEquiv]
    rw [SemidirectProduct.card, Nat.card_prod]
    norm_num [Nat.card_zmod]
  rw [hindex] at hfactor
  omega

/-- The central order-two axis in the split section map, before returning
to the literal quotient `U/N`. -/
noncomputable def degreeThreeFourBlockTwoSignSectionSemidirectCentralAxis
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    (hkernel_ne :
      (degreeThreeFourBlockTwoSignSectionComplementD8Map
        block P hr hs hcomponent hbinary htwo N).ker ≠ ⊥) :
    CentralOrderTwoKernelAxis
      (degreeThreeFourBlockTwoSignSectionSemidirectMap
        block P hr hs hcomponent hbinary htwo N) :=
  SemidirectBinaryKernelCentralAxis.ofTopKernel
    (degreeThreeFourBlockTwoSignSectionKernelTernaryEquiv
      block P hr hs hcomponent hbinary htwo N)
    (degreeThreeFourBlockTwoSignSectionComplementD8Map
      block P hr hs hcomponent hbinary htwo N)
    (degreeThreeFourBlockTwoSignSectionSemidirect_compatible
      block P hr hs hcomponent hbinary htwo N)
    (degreeThreeFourBlockTwoSignSectionComplement_isPGroup
      block P hr hs hcomponent hbinary N)
    hkernel_ne
    (degreeThreeFourBlockTwoSignSectionComplementD8Map_kernel_card_le_four
      block P hr hs hcomponent hbinary htwo N)

/-- Postcompose the split-section axis with the canonical equivalence from
the semidirect model to the literal degree-six wreath group. -/
noncomputable def degreeThreeFourBlockTwoSignSectionSplitWreathCentralAxis
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    (hkernel_ne :
      (degreeThreeFourBlockTwoSignSectionComplementD8Map
        block P hr hs hcomponent hbinary htwo N).ker ≠ ⊥) :
    CentralOrderTwoKernelAxis
      (DegreeSixS3Wreath.semidirectEquiv.symm.toMonoidHom.comp
        (degreeThreeFourBlockTwoSignSectionSemidirectMap
          block P hr hs hcomponent hbinary htwo N)) :=
  (degreeThreeFourBlockTwoSignSectionSemidirectCentralAxis
    block P hr hs hcomponent hbinary htwo N hkernel_ne).postcomp
      DegreeSixS3Wreath.semidirectEquiv.symm.toMonoidHom
      DegreeSixS3Wreath.semidirectEquiv.symm.injective

/-- The literal section map agrees with the split wreath map after applying
the chosen Schur-complement equivalence. -/
theorem degreeThreeFourBlockTwoSignSectionWreathMap_comp_semidirectEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    let H := degreeThreeFourBlockTwoSignSectionComplement
      block P hr hs hcomponent hbinary N
    let e := degreeThreeFourBlockTwoSignSectionSemidirectEquiv
      block P N H
        (degreeThreeFourBlockTwoSignSectionComplement_isComplement
          block P hr hs hcomponent hbinary N)
    (degreeThreeFourBlockTwoSignSectionWreathMap
        block P hr hs hcomponent hbinary htwo N).comp e.toMonoidHom =
      DegreeSixS3Wreath.semidirectEquiv.symm.toMonoidHom.comp
        (degreeThreeFourBlockTwoSignSectionSemidirectMap
          block P hr hs hcomponent hbinary htwo N) := by
  dsimp only
  apply MonoidHom.ext
  intro x
  simp only [degreeThreeFourBlockTwoSignSectionWreathMap,
    MonoidHom.comp_apply, MulEquiv.apply_symm_apply]

/-- If no binary kernel remains in the chosen complement, the literal
section-to-wreath epimorphism is an isomorphism. -/
theorem degreeThreeFourBlockTwoSignSectionWreathMap_injective_of_topKernel_eq_bot
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    (hkernel :
      (degreeThreeFourBlockTwoSignSectionComplementD8Map
        block P hr hs hcomponent hbinary htwo N).ker = ⊥) :
    Function.Injective
      (degreeThreeFourBlockTwoSignSectionWreathMap
        block P hr hs hcomponent hbinary htwo N) := by
  let H := degreeThreeFourBlockTwoSignSectionComplement
    block P hr hs hcomponent hbinary N
  let e := degreeThreeFourBlockTwoSignSectionSemidirectEquiv
    block P N H
      (degreeThreeFourBlockTwoSignSectionComplement_isComplement
        block P hr hs hcomponent hbinary N)
  have htop : Function.Injective
      (degreeThreeFourBlockTwoSignSectionComplementD8Map
        block P hr hs hcomponent hbinary htwo N) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hkernel
  have hsplit : Function.Injective
      (degreeThreeFourBlockTwoSignSectionSemidirectMap
        block P hr hs hcomponent hbinary htwo N) :=
    SemidirectBinaryKernelCentralAxis.map_injective
      (degreeThreeFourBlockTwoSignSectionKernelTernaryEquiv
        block P hr hs hcomponent hbinary htwo N).toMonoidHom
      (degreeThreeFourBlockTwoSignSectionComplementD8Map
        block P hr hs hcomponent hbinary htwo N)
      (degreeThreeFourBlockTwoSignSectionSemidirect_compatible
        block P hr hs hcomponent hbinary htwo N)
      (degreeThreeFourBlockTwoSignSectionKernelTernaryEquiv
        block P hr hs hcomponent hbinary htwo N).injective
      htop
  intro x y hxy
  apply e.symm.injective
  apply hsplit
  apply DegreeSixS3Wreath.semidirectEquiv.symm.injective
  simpa only [degreeThreeFourBlockTwoSignSectionWreathMap,
    MonoidHom.comp_apply, MulEquiv.apply_symm_apply] using hxy

/-- The central order-two axis transported back to the actual quotient
section. -/
noncomputable def degreeThreeFourBlockTwoSignSectionWreathCentralAxis
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    (hkernel_ne :
      (degreeThreeFourBlockTwoSignSectionComplementD8Map
        block P hr hs hcomponent hbinary htwo N).ker ≠ ⊥) :
    CentralOrderTwoKernelAxis
      (degreeThreeFourBlockTwoSignSectionWreathMap
        block P hr hs hcomponent hbinary htwo N) := by
  let H := degreeThreeFourBlockTwoSignSectionComplement
    block P hr hs hcomponent hbinary N
  let e := degreeThreeFourBlockTwoSignSectionSemidirectEquiv
    block P N H
      (degreeThreeFourBlockTwoSignSectionComplement_isComplement
        block P hr hs hcomponent hbinary N)
  exact
    (degreeThreeFourBlockTwoSignSectionSplitWreathCentralAxis
      block P hr hs hcomponent hbinary htwo N hkernel_ne).mapDomainEquiv
        e
        (degreeThreeFourBlockTwoSignSectionWreathMap
          block P hr hs hcomponent hbinary htwo N)
        (degreeThreeFourBlockTwoSignSectionWreathMap_comp_semidirectEquiv
          block P hr hs hcomponent hbinary htwo N)

/-- The nontrivial kernel case has the two-step central series required by
the recursive `QStar` comparison. -/
noncomputable def degreeThreeFourBlockTwoSignSectionWreathKernelCentralSeries
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    (hkernel_ne :
      (degreeThreeFourBlockTwoSignSectionComplementD8Map
        block P hr hs hcomponent hbinary htwo N).ker ≠ ⊥) :
    BinaryNormalKernelCentralSeries
      (G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N)
      (degreeThreeFourBlockTwoSignSectionWreathMap
        block P hr hs hcomponent hbinary htwo N).ker :=
  (degreeThreeFourBlockTwoSignSectionWreathCentralAxis
    block P hr hs hcomponent hbinary htwo N hkernel_ne).toCentralSeries
      (degreeThreeFourBlockTwoSignSectionWreathMap_kernel_card_le_four
        block P hr hs hcomponent hbinary htwo N)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
