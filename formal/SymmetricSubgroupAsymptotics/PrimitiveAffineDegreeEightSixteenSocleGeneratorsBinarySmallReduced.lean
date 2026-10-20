import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSixteenSocleGenerators
import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryExceptionalLocalBinarySmallReduced

/-! Isolated binary-small consumer route. Original datatypes, interfaces,
and finite certificate declarations are imported unchanged. Only the
changed consumer declarations and their private helper closure are copied. -/
set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu

namespace PrimitiveAffineImprimitiveBlockTransfer

namespace BinarySmallReduced

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

theorem degreeEight_retainedElementary_normalGen_le
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : BinaryAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hr : Nat.card block.Fibre = 8)
    (hsoluble : IsSolvable (P.complement (origin block)))
    (i₀ : block.Points)
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U))
    (hretained : ¬ E block P ≤ N.1) :
    MarkedC4.normalGen
      (minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
        (fun M => M ≤ binaryAffineTranslationImage block P N)) ≤
      Nat.card block.Points := by
  change MarkedC4.normalGen
      (finiteGroupSoclePart (preE7NonPairAction w U ⧸ N.1)
        (binaryAffineTranslationImage block P N)) ≤ Nat.card block.Points
  exact normalGen_finiteGroupSoclePart_le_of_card
    (preE7NonPairAction w U ⧸ N.1)
    (binaryAffineTranslationImage block P N) 8
    (Nat.card block.Points) (by norm_num)
    (fun M hM hME => _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.degreeEight_translationMinimal_card_le_of_clifford
      block P hClifford hTraceyPerm published shape hr hsoluble i₀ N
        hretained M hM hME)
    ((translationImage_card_le_coordinateProduct block P N).trans (by rw [hr]))

theorem degreeSixteen_retainedElementary_normalGen_le
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : BinaryAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hr : Nat.card block.Fibre = 16)
    (hsoluble : IsSolvable (P.complement (origin block)))
    (i₀ : block.Points)
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U))
    (hretained : ¬ E block P ≤ N.1) :
    MarkedC4.normalGen
      (minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
        (fun M => M ≤ binaryAffineTranslationImage block P N)) ≤
      2 * Nat.card block.Points := by
  change MarkedC4.normalGen
      (finiteGroupSoclePart (preE7NonPairAction w U ⧸ N.1)
        (binaryAffineTranslationImage block P N)) ≤
      2 * Nat.card block.Points
  exact normalGen_finiteGroupSoclePart_le_of_card
    (preE7NonPairAction w U ⧸ N.1)
    (binaryAffineTranslationImage block P N) 4
    (2 * Nat.card block.Points) (by norm_num)
    (fun M hM hME => _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.degreeSixteen_translationMinimal_card_le_of_clifford
      block P hClifford hTraceyPerm published shape hr hsoluble i₀ N
        hretained M hM hME)
    ((translationImage_card_le_coordinateProduct block P N).trans (by
      rw [hr, show 16 = 4 ^ (2 : ℕ) by norm_num, pow_mul]))

noncomputable def binaryAffineExceptional_socleNormalGeneratorBound
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : BinaryAffineSmallCatalogueData)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block)))
    (i₀ : block.Points)
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U))
    (hretained : ¬ E block P ≤ N.1) :
    SocleNormalGeneratorBound
      (preE7NonPairAction w U ⧸ N.1)
      (binaryAffineExceptionalSlots
        (Nat.card block.Fibre) (Nat.card block.Points)) := by
  apply (socleNormalGeneratorBound_iff_normalGen_le
    (preE7NonPairAction w U ⧸ N.1)
    (binaryAffineExceptionalSlots
      (Nat.card block.Fibre) (Nat.card block.Points))).2
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let N' : Subgroup S.A := N.1
  letI : N'.Normal := by dsimp only [N']; exact N.2
  have hirr : Representation.IsIrreducible
      (CliffordHomogeneousRestriction.localRepresentation
        S (localMap block P) (localMap_surjective block P) C).ρ := by
    rw [cliffordLocalRepresentation_rho_eq block P hTraceyPerm]
    exact binaryAffineLocalLinearRepresentation_irreducible block P
  have hfaith : Function.Injective
      (CliffordHomogeneousRestriction.localRepresentation
        S (localMap block P) (localMap_surjective block P) C).ρ := by
    rw [cliffordLocalRepresentation_rho_eq block P hTraceyPerm]
    exact binaryAffineLocalLinearRepresentation_injective block P
  have hcoord : ∀ i : block.Points,
      (CliffordHomogeneousRestriction.linearCoordinate
        S (localMap block P) i).range ≠ ⊥ := by
    intro i
    simpa only [S, CliffordHomogeneousRestriction.linearCoordinate,
      CliffordHomogeneousRestriction.linearBlockKernel, initialState,
      quotientEmbedding] using
        (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.binaryAffineLinearBlockKernelCoordinate_range_ne_bot
          block P published shape hsoluble i)
  have hretained' : ¬ CliffordHomogeneousRestriction.elementaryKernel
      S (localMap block P) ≤ N' := by
    simpa only [N', S, C,
      CliffordHomogeneousRestriction.elementaryKernel,
      ActualWreathAffineCapacity.K, initialState] using hretained
  have hmax := hClifford.normalGen_socle_le_max_retainedElementary_coreCentral
    S (localMap block P) (localMap_surjective block P) C
    hirr hfaith hcoord N' hretained'
  refine hmax.trans ?_
  apply max_le
  · change MarkedC4.normalGen
      (minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
        (fun M => M ≤ binaryAffineTranslationImage block P N)) ≤ _
    cases shape with
    | degreeEight hr hs =>
        rw [BinaryAffineExceptionalShape.slots_eq_of_degreeEight
          (.degreeEight hr hs) hr]
        exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.degreeEight_retainedElementary_normalGen_le block P hClifford
          hTraceyPerm published (.degreeEight hr hs) hr hsoluble i₀ N hretained
    | degreeSixteen hr hs =>
        rw [BinaryAffineExceptionalShape.slots_eq_of_degreeSixteen
          (.degreeSixteen hr hs) hr]
        exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.degreeSixteen_retainedElementary_normalGen_le block P hClifford
          hTraceyPerm published (.degreeSixteen hr hs) hr hsoluble i₀ N hretained
  · let H := trivialActionSoclePart
      (preE7NonPairAction w U ⧸ N.1)
      (binaryAffineRetainedCore block P N)
    letI : H.Normal := by
      dsimp only [H]
      infer_instance
    have hdisjoint : H ⊓ binaryAffineRetainedCore block P N = ⊥ := by
      simpa only [H, N', S,
        binaryAffineRetainedCore, binaryAffineCorePreimage,
        CliffordHomogeneousRestriction.retainedCoreImage,
        CliffordHomogeneousRestriction.corePreimage,
        CliffordHomogeneousRestriction.linearBlockKernel,
        initialState, quotientEmbedding] using
          hClifford.trivialActionSoclePart_inf_retainedCore_eq_bot
            S (localMap block P) (localMap_surjective block P) C
            hirr hfaith hcoord N' hretained'
    have htop : MarkedC4.normalGen H ≤ Nat.card block.Points :=
      binaryAffineCoreDisjoint_normalGen_le block P hgen N H hdisjoint
    cases shape with
    | degreeEight hr hs =>
        rw [BinaryAffineExceptionalShape.slots_eq_of_degreeEight
          (.degreeEight hr hs) hr]
        exact htop
    | degreeSixteen hr hs =>
        rw [BinaryAffineExceptionalShape.slots_eq_of_degreeSixteen
          (.degreeSixteen hr hs) hr]
        exact htop.trans
          (Nat.le_mul_of_pos_left (Nat.card block.Points) (by norm_num))

end BinarySmallReduced

end PrimitiveAffineImprimitiveBlockTransfer

end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

end

