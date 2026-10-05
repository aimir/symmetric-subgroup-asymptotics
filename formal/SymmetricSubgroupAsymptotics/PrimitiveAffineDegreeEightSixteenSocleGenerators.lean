import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryExceptionalLocal
import SymmetricSubgroupAsymptotics.WholeLinearKernelSocleSharing

/-!
# Whole-socle generators in affine degrees eight and sixteen

This is the thin consumer of the literal local calculation.  The checked
whole-kernel theorem shares generator slots between the socle carried by the
actual translation intersection and the socle centralized by the retained
linear core.  The latter embeds in a section of the actual permutation top.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
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

/-! ## Literal whole core and block-top section -/

abbrev binaryAffineCorePreimage :
    Subgroup (preE7NonPairAction w U) :=
  (binaryAffineLinearBlockKernel block P).comap
    (QuotientGroup.mk' (E block P))

instance binaryAffineCorePreimage_normal :
    (binaryAffineCorePreimage block P).Normal := by
  dsimp only [binaryAffineCorePreimage]
  infer_instance

def binaryAffineOriginalTopMap :
    preE7NonPairAction w U →* block.Top :=
  (binaryAffineQuotientTopMap block P).comp
    (QuotientGroup.mk' (E block P))

theorem binaryAffineOriginalTopMap_surjective :
    Function.Surjective (binaryAffineOriginalTopMap block P) :=
  (binaryAffineQuotientTopMap_surjective block P).comp
    (QuotientGroup.mk'_surjective (E block P))

theorem binaryAffineOriginalTopMap_ker :
    (binaryAffineOriginalTopMap block P).ker =
      binaryAffineCorePreimage block P := by
  rfl

instance binaryAffineTopImage_normal
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U)) :
    ((binaryAffineCorePreimage block P ⊔ N.1).map
      (binaryAffineOriginalTopMap block P)).Normal :=
  Subgroup.Normal.map inferInstance (binaryAffineOriginalTopMap block P)
    (binaryAffineOriginalTopMap_surjective block P)

abbrev binaryAffineRetainedCore
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  (binaryAffineCorePreimage block P).map (QuotientGroup.mk' N.1)

instance binaryAffineRetainedCore_normal
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U)) :
    (binaryAffineRetainedCore block P N).Normal :=
  Subgroup.Normal.map inferInstance (QuotientGroup.mk' N.1)
    (QuotientGroup.mk'_surjective N.1)

def binaryAffineRetainedTopMap
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U)) :
    (preE7NonPairAction w U ⧸ N.1) →*
      preE7NonPairAction w U ⧸
        (binaryAffineCorePreimage block P ⊔ N.1) :=
  QuotientGroup.lift N.1
    (QuotientGroup.mk' (binaryAffineCorePreimage block P ⊔ N.1)) (by
      rw [QuotientGroup.ker_mk']
      exact le_sup_right)

theorem binaryAffineRetainedTopMap_surjective
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U)) :
    Function.Surjective (binaryAffineRetainedTopMap block P N) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (binaryAffineCorePreimage block P ⊔ N.1) q
  exact ⟨QuotientGroup.mk' N.1 g, rfl⟩

theorem binaryAffineRetainedTopMap_ker
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U)) :
    (binaryAffineRetainedTopMap block P N).ker =
      binaryAffineRetainedCore block P N := by
  rw [binaryAffineRetainedTopMap, QuotientGroup.ker_lift,
    QuotientGroup.ker_mk', Subgroup.map_sup,
    QuotientGroup.map_mk'_self, sup_bot_eq]

def binaryAffineRestrictedRetainedTopMap
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) :
    H →* preE7NonPairAction w U ⧸
      (binaryAffineCorePreimage block P ⊔ N.1) :=
  (binaryAffineRetainedTopMap block P N).comp H.subtype

theorem binaryAffineRestrictedRetainedTopMap_injective_of_disjoint
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hdisjoint : H ⊓ binaryAffineRetainedCore block P N = ⊥) :
    Function.Injective
      (binaryAffineRestrictedRetainedTopMap block P N H) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro x hx
    have hxD : (x.1 : preE7NonPairAction w U ⧸ N.1) ∈
        binaryAffineRetainedCore block P N := by
      rw [← binaryAffineRetainedTopMap_ker block P N]
      exact MonoidHom.mem_ker.mp hx
    have hxInf : (x.1 : preE7NonPairAction w U ⧸ N.1) ∈
        H ⊓ binaryAffineRetainedCore block P N := ⟨x.2, hxD⟩
    rw [hdisjoint] at hxInf
    exact Subtype.ext (Subgroup.mem_bot.mp hxInf)
  · exact bot_le

def binaryAffineRetainedTopEquivBlockQuotient
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U)) :
    (preE7NonPairAction w U ⧸
        (binaryAffineCorePreimage block P ⊔ N.1)) ≃*
      (block.Top ⧸
        ((binaryAffineCorePreimage block P ⊔ N.1).map
          (binaryAffineOriginalTopMap block P))) :=
  quotientEquivOfKerLe (binaryAffineOriginalTopMap block P)
    (binaryAffineOriginalTopMap_surjective block P)
    (binaryAffineCorePreimage block P ⊔ N.1) (by
      rw [binaryAffineOriginalTopMap_ker block P]
      exact le_sup_left)

def binaryAffinePermutationTopSectionMap
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U)) :
    block.Top →*
      preE7NonPairAction w U ⧸
        (binaryAffineCorePreimage block P ⊔ N.1) :=
  (binaryAffineRetainedTopEquivBlockQuotient
      (block := block) (P := P) N).symm.toMonoidHom.comp
    (QuotientGroup.mk'
      ((binaryAffineCorePreimage block P ⊔ N.1).map
        (binaryAffineOriginalTopMap block P)))

theorem binaryAffinePermutationTopSectionMap_surjective
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U)) :
    Function.Surjective (binaryAffinePermutationTopSectionMap block P N) :=
  (binaryAffineRetainedTopEquivBlockQuotient
      (block := block) (P := P) N).symm.surjective.comp
    (QuotientGroup.mk'_surjective
      ((binaryAffineCorePreimage block P ⊔ N.1).map
        (binaryAffineOriginalTopMap block P)))

theorem binaryAffineCoreDisjoint_normalGen_le
    (hgen : PermutationSubgroupGeneratorBound)
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) [H.Normal]
    (hdisjoint : H ⊓ binaryAffineRetainedCore block P N = ⊥) :
    MarkedC4.normalGen H ≤ Nat.card block.Points := by
  let pointEquiv : block.Points ≃ Fin (Nat.card block.Points) :=
    Finite.equivFin block.Points
  let τ : block.Top →* Equiv.Perm (Fin (Nat.card block.Points)) :=
    pointEquiv.permCongrHom.toMonoidHom.comp block.Top.subtype
  have hτ : Function.Injective τ :=
    pointEquiv.permCongrHom.injective.comp Subtype.val_injective
  let R : Subgroup (Equiv.Perm (Fin (Nat.card block.Points))) := τ.range
  let eR : block.Top ≃* R := MulEquiv.ofBijective τ.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr hτ,
      τ.rangeRestrict_surjective⟩
  let q : R →*
      preE7NonPairAction w U ⧸
        (binaryAffineCorePreimage block P ⊔ N.1) :=
    (binaryAffinePermutationTopSectionMap block P N).comp
      eR.symm.toMonoidHom
  have hq : Function.Surjective q :=
    (binaryAffinePermutationTopSectionMap_surjective block P N).comp
      eR.symm.surjective
  exact normalGen_normalSubgroup_le_degree_of_permutationSection hgen
    R q hq H (binaryAffineRestrictedRetainedTopMap block P N H)
    (binaryAffineRestrictedRetainedTopMap_injective_of_disjoint
      block P N H hdisjoint)
    (by simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2)

/-! ## Translation-carried and whole socle -/

theorem degreeEight_retainedElementary_normalGen_le
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : PublishedPrimitiveAffineSmallCatalogueData)
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
    (fun M hM hME => degreeEight_translationMinimal_card_le_of_clifford
      block P hClifford hTraceyPerm published shape hr hsoluble i₀ N
        hretained M hM hME)
    ((translationImage_card_le_coordinateProduct block P N).trans (by rw [hr]))

theorem degreeSixteen_retainedElementary_normalGen_le
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : PublishedPrimitiveAffineSmallCatalogueData)
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
    (fun M hM hME => degreeSixteen_translationMinimal_card_le_of_clifford
      block P hClifford hTraceyPerm published shape hr hsoluble i₀ N
        hretained M hM hME)
    ((translationImage_card_le_coordinateProduct block P N).trans (by
      rw [hr, show 16 = 4 ^ (2 : ℕ) by norm_num, pow_mul]))

/-- Sharp whole-socle tuple for all five soluble binary exceptional cells. -/
noncomputable def binaryAffineExceptional_socleNormalGeneratorBound
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (published : PublishedPrimitiveAffineSmallCatalogueData)
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
        (binaryAffineLinearBlockKernelCoordinate_range_ne_bot
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
        exact degreeEight_retainedElementary_normalGen_le block P hClifford
          hTraceyPerm published (.degreeEight hr hs) hr hsoluble i₀ N hretained
    | degreeSixteen hr hs =>
        rw [BinaryAffineExceptionalShape.slots_eq_of_degreeSixteen
          (.degreeSixteen hr hs) hr]
        exact degreeSixteen_retainedElementary_normalGen_le block P hClifford
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

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
