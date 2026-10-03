import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveBlockTransfer
import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity
import SymmetricSubgroupAsymptotics.ActualWreathCompressionTrace
import SymmetricSubgroupAsymptotics.PrimitiveCompositionLengthTransport
import SymmetricSubgroupAsymptotics.RelativeCompleteSourcePreE7Bridge
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput
import SymmetricSubgroupAsymptotics.TraceyRefinedAffineInput
import SymmetricSubgroupAsymptotics.PermutationPrimeGroupRank

/-!
# Transfer an affine component source through its actual block system

This is the construction-facing imprimitive affine theorem.  A source on the
literal affine component consists of the induced-section capacity used at
each of its actual local chief factors, the resulting unpadded linear margin,
and the finite coefficient estimate.  The theorem transports that source
through the standard embedding attached to the chosen original block map,
derives the padded moment parameters, and returns a source for the original
ambient action.

Nothing here reindexes the component as a `PreE7NonPairActionClass`.  The
construction therefore includes local degrees two, three and four, and it
also includes components which are 2-groups.  Elementary `C2` chief factors
are compressed through their actual correlated coordinate submodules; the
endpoint is the faithful action on the original set of blocks.
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

/-- Initial compression state coming from the actual selected block map. -/
def initialState
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) :
    ActualWreathCompressionState block.Top block.Points := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp
      (show 1 < Nat.card block.Fibre by
        have := block.degrees_ge_two.1
        omega)
  have hw : 2 ≤ w := by
    rw [width_eq block]
    have hprod := Nat.mul_le_mul block.degrees_ge_two.1
      block.degrees_ge_two.2
    omega
  have htrans : ∀ x y : Fin w,
      ∃ g : preE7NonPairAction w U,
        MulAction.toPermHom (preE7NonPairAction w U) (Fin w) g x = y := by
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
      (preE7NonPairAction w U) x y
    exact ⟨g, hg⟩
  let generatorData := hTraceyPerm.exists_generating_tuple w
    (preE7NonPairAction w U)
    (MulAction.toPermHom (preE7NonPairAction w U) (Fin w))
    (show Function.Injective
      (MulAction.toPermHom (preE7NonPairAction w U) (Fin w)) from
        MulAction.toPerm_injective)
    hw htrans
  exact
    { A := preE7NonPairAction w U
      D := block.Component
      groupA := inferInstance
      finiteA := inferInstance
      groupD := inferInstance
      finiteD := inferInstance
      rho := ambientEmbedding block
      rho_injective := ambientEmbedding_injective block
      sourceDegree := w
      generatorCount := traceyPermutationGeneratorCeiling w
      generators := Classical.choose generatorData
      generators_full := Classical.choose_spec generatorData
      sectionalRank := by
        intro p hp K
        exact primeRank_le_of_subgroup p (preE7NonPairAction w U) K
      top_surjective := by
        intro q
        obtain ⟨a, ha⟩ := q.2
        refine ⟨a, Subtype.ext ?_⟩
        simpa only [ambientEmbedding, ActualBlockWreathEmbedding.embedding]
          using ha
      top_pretransitive := block.top_pretransitive
      fullComponent := ActualBlockWreathEmbedding.fullComponent
        block.map block.map_equivariant block.base }

/-- The common elementary-capacity input on the selected real block
system. -/
noncomputable def affineCapacityInput
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) :
    ActualWreathElementaryCapacityInput
      (Q := block.Top) (I := block.Points) :=
  ActualWreathAffineCapacity.elementaryCapacityInput
    hTraceyHalf hTraceyLog hTraceyRefined (by
      simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2)

/-- The traced residual tower after removing the regular affine
translations.  Its local group is literally `Component / V`. -/
noncomputable def affineQuotientTrace
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    [Nontrivial block.Fibre]
    (P : PrimitiveAffineProfile block.Component block.Fibre) :
    ActualWreathCompressionTrace
      ((initialState hTraceyPerm block).quotient
        (block.Component ⧸ P.V) (QuotientGroup.mk' P.V)
          (QuotientGroup.mk'_surjective P.V)) :=
  ActualWreathCompressionTrace.canonicalOfCapacity
    (affineCapacityInput hTraceyHalf hTraceyLog hTraceyRefined block)
    ((initialState hTraceyPerm block).quotient
      (block.Component ⧸ P.V) (QuotientGroup.mk' P.V)
        (QuotientGroup.mk'_surjective P.V))

/-- The affine-native traced tower.  Primitivity makes the regular
translation subgroup a minimal normal subgroup, so we may and do take it as
the first literal chief edge.  The remainder is the ordinary canonical
tower on the quotient, which is the point stabilizer up to the standard
affine quotient equivalence. -/
noncomputable def affineTrace
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) :
    ActualWreathCompressionTrace (initialState hTraceyPerm block) := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let S := initialState hTraceyPerm block
  let capacity := affineCapacityInput hTraceyHalf hTraceyLog hTraceyRefined block
  let C₀ := P.elementaryChart block.component_preprimitive
  let D' := block.Component ⧸ P.V
  let phi : block.Component →* D' := QuotientGroup.mk' P.V
  have hphi : Function.Surjective phi := QuotientGroup.mk'_surjective P.V
  have hker : phi.ker = P.V := QuotientGroup.ker_mk' P.V
  let C : ElementaryMinimalNormalChart phi.ker :=
    { p := P.p
      p_prime := P.p_prime
      primeFact := C₀.primeFact
      V := C₀.V
      addCommGroup := C₀.addCommGroup
      module := C₀.module
      finiteDimensional := C₀.finiteDimensional
      equiv := (MulEquiv.subgroupCongr hker).trans C₀.equiv }
  let H := Classical.choose (capacity S D' phi hphi C)
  have hH := Classical.choose_spec (capacity S D' phi hphi C)
  have hhalf := hH.1
  have hlog := hH.2.1
  have hrefined := hH.2.2.1
  have hintegral := hH.2.2.2.1
  have hcoeff := hH.2.2.2.2
  let next := affineQuotientTrace hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P
  have hVne : P.V ≠ ⊥ := by
    haveI : Nontrivial C₀.V := C₀.nontrivial
    exact P.V.nontrivial_iff_ne_bot.mp C₀.equiv.symm.injective.nontrivial
  let c := prependMinimalNormalChiefSeries P.V hVne
    (fun K hK hKV => P.minimal block.component_preprimitive K hK hKV)
    next.chief
  have hc := prependMinimalNormalChiefSeries_abelianLength P.V hVne
    (fun K hK hKV => P.minimal block.component_preprimitive K hK hKV)
    next.chief
  refine
    { tower := .elementary S D' phi hphi C H hhalf hlog hrefined hcoeff
        next.tower
      integralCapacities := ⟨hintegral, next.integralCapacities⟩
      chief := c
      abelianLength_eq := ?_ }
  change Module.finrank (ZMod C.p) C.V + next.tower.abelianLength =
    actualChiefSeriesAbelianLength c
  rw [hc, next.abelianLength_eq]
  congr 1
  letI : Fact P.p.Prime := C₀.primeFact
  exact (chiefAbelianLength_elementary C₀.equiv).symm

/-- The affine-native trace exposes the translation dimension followed by
the literal quotient trace. -/
theorem affineTrace_abelianLength_eq
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    [Nontrivial block.Fibre]
    (P : PrimitiveAffineProfile block.Component block.Fibre) :
    (affineTrace hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P).tower.abelianLength =
      (P.elementaryChart block.component_preprimitive).d +
        (affineQuotientTrace hTraceyHalf hTraceyLog hTraceyRefined
          hTraceyPerm block P).tower.abelianLength := by
  rfl

/-- The group-native source carried by an affine primitive component.  Its
capacity field is evaluated on all quotient states of the same real block
system.  Its only project estimate is the affine capacity margin.  The
finite coefficient bound is a theorem of the actual chief tower and is
derived in `PrimitiveAffineImprimitiveCoefficient`; it is not source data. -/
structure ComponentSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (_P : PrimitiveAffineProfile block.Component block.Fibre) : Type 1 where
  margin :
    let trace := affineTrace hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block _P
    let tower := trace.tower
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - tower.envelope.v) / 8 - tower.envelope.eta

namespace ComponentSource

variable
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

/-- The elementary-layer capacity is a theorem, uniformly over all quotient
states of the selected block system. -/
noncomputable def capacity : ActualWreathElementaryCapacityInput
    (Q := block.Top) (I := block.Points) :=
  affineCapacityInput hTraceyHalf hTraceyLog hTraceyRefined block

/-- The literal local-chief trace selected by the component source.  Its
first edge is the regular affine translation subgroup.  This is the natural
chief edge forced by primitivity and keeps the published small-complement
catalogue available on the remaining quotient. -/
noncomputable def trace :
  ActualWreathCompressionTrace (initialState hTraceyPerm block) :=
  affineTrace hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P

/-- The compression tower underlying the traced local chief series. -/
noncomputable def tower :
  ActualWreathCompressionTower (initialState hTraceyPerm block) :=
  (trace hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P).tower

/-- Complete quotient-weight transfer from the original ambient group to
the faithful action of the actual top on the original blocks. -/
noncomputable def envelope :
    RelativeCompleteSourceEnvelope (preE7NonPairAction w U) :=
  (tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P).envelope

/-- The actual affine exponent is bounded by the published primitive
composition-length expression.  The composition series is transported from
the literal block fibre to `Fin r`; no project-owned density premise is used. -/
theorem envelope_eta_le_primitiveCompositionBound
    (hcomp : PrimitiveCompositionLengthInput) :
    (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P).eta ≤
      fixedTargetCompositionGamma *
        ((Nat.card block.Points : ℝ) / 2) *
          ((8 / 3 : ℝ) * Real.logb 2 (Nat.card block.Fibre) - 4 / 3) := by
  obtain ⟨t, htower⟩ :=
    (trace hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P).envelope_eta_le_some_compositionLength
  have ht := PrimitiveCompositionLengthInput.bound_of_equiv hcomp
    (Nat.card block.Fibre) block.degrees_ge_two.1
    (Finite.equivFin block.Fibre) block.Component
    block.component_preprimitive t
  have hfactor : 0 ≤ fixedTargetCompositionGamma *
      ((Fintype.card block.Points : ℝ) / 2) := by
    apply mul_nonneg
    · exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num))
        (by norm_num)
    · positivity
  simpa only [Fintype.card_eq_nat_card] using
    htower.trans (mul_le_mul_of_nonneg_left ht hfactor)

end ComponentSource

/-- Correct construction target for every imprimitive affine component.
The generic capacity alternative alone is false in the small exceptional
block cells, so the target also permits an already integrated ambient owner.
No literature interface is allowed to return this project-owned sum. -/
structure PreE7PrimitiveAffineImprimitiveComponentSourceData
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) : Type 1 where
  source : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    (P : PrimitiveAffineProfile block.Component block.Fibre) →
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PreE7RankTailSourceOrYonedaTopData w U

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
