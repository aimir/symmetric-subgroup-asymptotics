import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineZeroCore
import SymmetricSubgroupAsymptotics.WholeLinearKernelSocleSharing

/-!
# The nonzero whole-core degree-nine row

When the actual linear block kernel is nonzero, transitivity makes every
literal local coordinate nonzero.  The published Clifford homogeneous
restriction theorem then identifies the socle factors on which that whole
kernel acts nontrivially with the factors carried by the literal translation
image.  Tracey's induced-module theorem bounds that part by one slot per
block; the centralized part embeds in the literal block top and has the same
bound.  The generic whole-kernel theorem pairs the two tuples by maximum.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev LiteralNormalAxis (G : Type) [Group G] :=
  {N : Subgroup G // N.Normal}

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-! ## Exact local representation -/

/-- The literal affine complement and the compressed local quotient are
canonically isomorphic through the faithful nonzero-translation action. -/
noncomputable def degreeNineLocalComplementEquiv :
    P.complement (origin block) ≃* LocalQuotient block P :=
  MulEquiv.ofBijective (complementAction block P).rangeRestrict
    ⟨(by
        intro x y hxy
        apply complementAction_injective block P
        exact congrArg Subtype.val hxy),
      (complementAction block P).rangeRestrict_surjective⟩

/-- The exact local complement representation transported to the literal
compressed local quotient. -/
noncomputable abbrev degreeNineLocalLinearRepresentation :
    Rep (ZMod P.p) (LocalQuotient block P) := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  exact Rep.of ((P.complementRepresentation
    (primitive block) C (origin block)).ρ.comp
      (degreeNineLocalComplementEquiv block P).symm.toMonoidHom)

theorem degreeNineLocalLinearRepresentation_injective :
    let C := chart block P
    letI : Fact P.p.Prime := C.primeFact
    Function.Injective (degreeNineLocalLinearRepresentation block P).ρ := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  exact (P.complementRepresentation_injective
    (primitive block) C (origin block)).comp
      (degreeNineLocalComplementEquiv block P).symm.injective

theorem degreeNineLocalLinearRepresentation_irreducible :
    let C := chart block P
    letI : Fact P.p.Prime := C.primeFact
    Representation.IsIrreducible
      (degreeNineLocalLinearRepresentation block P).ρ := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  letI : Representation.IsIrreducible
      (P.complementRepresentation
        (primitive block) C (origin block)).ρ :=
    P.complementRepresentation_irreducible
      (primitive block) C (origin block)
  exact representation_irreducible_comp
    (P.complementRepresentation
      (primitive block) C (origin block)).ρ
    (degreeNineLocalComplementEquiv block P).symm.toMonoidHom
    (degreeNineLocalComplementEquiv block P).symm.surjective

/-- Pointwise comparison between the generic Clifford local representation
and the literal affine-complement representation.  Keeping the coordinate
calculation pointwise prevents the elaborator from repeatedly unfolding the
two representation structures under a broad extensionality proof. -/
theorem degreeNineCliffordLocalRepresentation_apply
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (q : LocalQuotient block P) (v : (chart block P).V) :
    let S := initialState hTraceyPerm block
    let C := localTranslationChart block P
    (CliffordHomogeneousRestriction.localRepresentation
      S (localMap block P) (localMap_surjective block P) C).ρ q v =
      (degreeNineLocalLinearRepresentation block P).ρ q v := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let ε := CliffordHomogeneousRestriction.localQuotientEquiv
    S (localMap block P) (localMap_surjective block P)
  let δ := degreeNineLocalComplementEquiv block P
  let c : P.complement (origin block) := δ.symm q
  have hcq : complementAction block P c = q :=
    congrArg Subtype.val (δ.apply_symm_apply q)
  have hlocal : localMap block P c.1 = q := by
    apply Subtype.ext
    simpa only [localMap, MonoidHom.comp_apply,
      P.complementProjection_complement] using hcq
  have hclass : ε.symm q =
      QuotientGroup.mk' (localMap block P).ker c.1 := by
    apply ε.injective
    rw [ε.apply_symm_apply]
    exact hlocal.symm
  let e : (localMap block P).ker :=
    localKernelEquiv block P (Multiplicative.ofAdd v)
  have he : C.equiv e = Multiplicative.ofAdd v := by
    change (localKernelEquiv block P).symm
      (localKernelEquiv block P (Multiplicative.ofAdd v)) = _
    exact (localKernelEquiv block P).symm_apply_apply
      (Multiplicative.ofAdd v)
  change C.quotientRepresentation.ρ (ε.symm q) v =
    (P.complementRepresentation
      (primitive block) (chart block P) (origin block)).ρ c v
  rw [hclass]
  apply Multiplicative.ofAdd.injective
  change Multiplicative.ofAdd
      (C.quotientRepresentation.ρ
        (QuotientGroup.mk' (localMap block P).ker c.1) v) =
    Multiplicative.ofAdd
      ((P.complementRepresentation
        (primitive block) (chart block P) (origin block)).ρ c v)
  have hev : (C.equiv e).toAdd = v :=
    congrArg Multiplicative.toAdd he
  conv_lhs =>
    rw [← hev, C.quotientRepresentation_apply]
  change C.equiv (MulAut.conjNormal c.1 e) = _
  rw [P.complementRepresentation_apply]
  simp only [ofAdd_toAdd]
  apply (localKernelEquiv block P).injective
  apply Subtype.ext
  rw [show C.equiv (MulAut.conjNormal c.1 e) =
      (localKernelEquiv block P).symm (MulAut.conjNormal c.1 e) by rfl,
    (localKernelEquiv block P).apply_symm_apply]
  change c.1 * e.1 * c.1⁻¹ =
    (((P.bottomKernelEquiv (primitive block) (chart block P) (origin block))
      ((chart block P).equiv
        (P.complementAction (origin block) c
          ((chart block P).equiv.symm (Multiplicative.ofAdd v)))) :
        (P.complementProjection (origin block)).ker) : block.Component)
  rw [P.bottomKernelEquiv_coe,
    (chart block P).equiv.symm_apply_apply]
  rw [show (e.1 : block.Component) =
      ((chart block P).equiv.symm (Multiplicative.ofAdd v) : P.V) by rfl]
  rfl

/-- Extensional wrapper around the preceding opaque pointwise comparison. -/
theorem degreeNineCliffordLocalRepresentation_rho_eq
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    let S := initialState hTraceyPerm block
    let C := localTranslationChart block P
    (CliffordHomogeneousRestriction.localRepresentation
      S (localMap block P) (localMap_surjective block P) C).ρ =
      (degreeNineLocalLinearRepresentation block P).ρ := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  apply MonoidHom.ext
  intro q
  apply LinearMap.ext
  intro v
  exact degreeNineCliffordLocalRepresentation_apply
    block P hTraceyPerm q v

/-! ## Clifford whole-core separation -/

/-- The action-specific hypotheses of the published Clifford theorem in
the nonzero whole-kernel branch. -/
theorem degreeNineWholeCore_cliffordData
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hK : degreeNineLinearBlockKernel block P ≠ ⊥)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hretained : ¬ E block P ≤ N.1) :
    let S := initialState hTraceyPerm block
    let C := localTranslationChart block P
    nontrivialActionSoclePart
        (preE7NonPairAction w U ⧸ N.1)
        (degreeNineWholeRetainedCore block P N) =
      degreeNineTranslationSoclePart block P N ∧
    trivialActionSoclePart
        (preE7NonPairAction w U ⧸ N.1)
        (degreeNineWholeRetainedCore block P N) ⊓
          degreeNineWholeRetainedCore block P N = ⊥ := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  have hirr : Representation.IsIrreducible
      (CliffordHomogeneousRestriction.localRepresentation
        S (localMap block P) (localMap_surjective block P) C).ρ := by
    rw [degreeNineCliffordLocalRepresentation_rho_eq
      block P hTraceyPerm]
    exact degreeNineLocalLinearRepresentation_irreducible block P
  have hinj : Function.Injective
      (CliffordHomogeneousRestriction.localRepresentation
        S (localMap block P) (localMap_surjective block P) C).ρ := by
    rw [degreeNineCliffordLocalRepresentation_rho_eq
      block P hTraceyPerm]
    exact degreeNineLocalLinearRepresentation_injective block P
  have hcoordinate : ∀ i : block.Points,
      (CliffordHomogeneousRestriction.linearCoordinate
        S (localMap block P) i).range ≠ ⊥ := by
    intro i
    simpa only [CliffordHomogeneousRestriction.linearCoordinate,
      CliffordHomogeneousRestriction.linearBlockKernel, S, initialState,
      quotientEmbedding] using
        (degreeNineLinearBlockKernelCoordinate_range_ne_bot_of_kernel_ne_bot
          block P hK i)
  have hactive := hClifford.nontrivialActionSoclePart_eq_retainedElementary
    S (localMap block P) (localMap_surjective block P) C
      hirr hinj hcoordinate N.1 hretained
  have hcentral := hClifford.trivialActionSoclePart_inf_retainedCore_eq_bot
    S (localMap block P) (localMap_surjective block P) C
      hirr hinj hcoordinate N.1 hretained
  constructor
  · simpa only [CliffordHomogeneousRestriction.retainedCoreImage,
      CliffordHomogeneousRestriction.retainedElementaryImage,
      CliffordHomogeneousRestriction.corePreimage,
      CliffordHomogeneousRestriction.linearBlockKernel,
      CliffordHomogeneousRestriction.elementaryKernel,
      ActualWreathAffineCapacity.K, S, initialState, quotientEmbedding,
      degreeNineWholeRetainedCore, degreeNineWholeCorePreimage,
      degreeNineTranslationSoclePart, finiteGroupSoclePart] using hactive
  · simpa only [CliffordHomogeneousRestriction.retainedCoreImage,
      CliffordHomogeneousRestriction.corePreimage,
      CliffordHomogeneousRestriction.linearBlockKernel,
      ActualWreathAffineCapacity.K, S, initialState, quotientEmbedding,
      degreeNineWholeRetainedCore, degreeNineWholeCorePreimage] using hcentral

/-- Complete nonzero whole-core socle-generator row. -/
theorem degreeNineNonzeroWholeCore_socleGenerators
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hs : 2 ≤ Nat.card block.Points)
    (hr : Nat.card block.Fibre = 9)
    (i₀ : block.Points)
    (hK : degreeNineLinearBlockKernel block P ≠ ⊥)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hretained : ¬ E block P ≤ N.1) :
    SocleNormalGeneratorBound
      (preE7NonPairAction w U ⧸ N.1) (Nat.card block.Points) := by
  apply (socleNormalGeneratorBound_iff_normalGen_le _ _).2
  let D := degreeNineWholeRetainedCore block P N
  have hsplit := degreeNineWholeCore_cliffordData block P hClifford
    hTraceyPerm hK N hretained
  have hmax := normalGen_finiteGroupSocle_le_max_actionSocleParts
    (preE7NonPairAction w U ⧸ N.1) D
  refine hmax.trans (max_le ?_ ?_)
  · rw [hsplit.1]
    exact degreeNineTranslationSoclePart_normalGen_le_tracey
      block P hTraceyHalf hTraceyPerm hr i₀ N
  · apply degreeNineWholeCoreDisjoint_normalGen_le block P hgen hs N
      (trivialActionSoclePart
        (preE7NonPairAction w U ⧸ N.1) D)
    exact hsplit.2

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
