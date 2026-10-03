import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveBlockTransfer
import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity
import SymmetricSubgroupAsymptotics.ActualWreathCompressionTrace
import SymmetricSubgroupAsymptotics.PrimitiveCompositionLengthTransport
import SymmetricSubgroupAsymptotics.RelativeCompleteSourcePreE7Bridge
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput
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

/-- The group-native source carried by an affine primitive component.  Its
capacity field is evaluated on all quotient states of the same real block
system.  The remaining two fields are precisely the mathematical estimates
on that constructed envelope: the affine capacity margin and its finite
coefficient bound.  The growing-transfer parameters are derived later and
are not included as assumptions. -/
structure ComponentSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (_P : PrimitiveAffineProfile block.Component block.Fibre) : Type 1 where
  margin :
    let capacity := ActualWreathAffineCapacity.elementaryCapacityInput
      (Q := block.Top) (I := block.Points) hTraceyHalf hTraceyLog (by
        simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2)
    let trace := ActualWreathCompressionTrace.canonicalOfCapacity
      capacity (initialState hTraceyPerm block)
    let tower := trace.tower
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - tower.envelope.v) / 8 - tower.envelope.eta
  coefficient_bound :
    let capacity := ActualWreathAffineCapacity.elementaryCapacityInput
      (Q := block.Top) (I := block.Points) hTraceyHalf hTraceyLog (by
        simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2)
    let trace := ActualWreathCompressionTrace.canonicalOfCapacity
      capacity (initialState hTraceyPerm block)
    let tower := trace.tower
    ∀ b, tower.envelope.coefficient b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace ComponentSource

variable
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

/-- The elementary-layer capacity is a theorem, uniformly over all quotient
states of the selected block system. -/
noncomputable def capacity : ActualWreathElementaryCapacityInput
    (Q := block.Top) (I := block.Points) :=
  ActualWreathAffineCapacity.elementaryCapacityInput hTraceyHalf hTraceyLog (by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2)

/-- The literal local-chief trace selected by the component source. -/
noncomputable def trace :
  ActualWreathCompressionTrace (initialState hTraceyPerm block) :=
  ActualWreathCompressionTrace.canonicalOfCapacity
    (capacity hTraceyHalf hTraceyLog block)
    (initialState hTraceyPerm block)

/-- The compression tower underlying the traced local chief series. -/
noncomputable def tower :
  ActualWreathCompressionTower (initialState hTraceyPerm block) :=
  (trace hTraceyHalf hTraceyLog hTraceyPerm block).tower

/-- Complete quotient-weight transfer from the original ambient group to
the faithful action of the actual top on the original blocks. -/
noncomputable def envelope :
    RelativeCompleteSourceEnvelope (preE7NonPairAction w U) :=
  (tower hTraceyHalf hTraceyLog hTraceyPerm block).envelope

/-- The actual affine exponent is bounded by the published primitive
composition-length expression.  The composition series is transported from
the literal block fibre to `Fin r`; no project-owned density premise is used. -/
theorem envelope_eta_le_primitiveCompositionBound
    (hcomp : PrimitiveCompositionLengthInput) :
    (envelope hTraceyHalf hTraceyLog hTraceyPerm block).eta ≤
      fixedTargetCompositionGamma *
        ((Nat.card block.Points : ℝ) / 2) *
          ((8 / 3 : ℝ) * Real.logb 2 (Nat.card block.Fibre) - 4 / 3) := by
  obtain ⟨t, htower⟩ :=
    (trace hTraceyHalf hTraceyLog hTraceyPerm block).envelope_eta_le_some_compositionLength
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

variable (S : ComponentSource hTraceyHalf hTraceyLog hTraceyPerm block P)

/-- The two component estimates, together with the structural facts proved
by the actual tower, give the exact numerical margin record expected by the
pre-E7 transfer. -/
noncomputable def preE7Margin :
    RelativeCompleteSourceEnvelope.PreE7Margin
      (envelope hTraceyHalf hTraceyLog hTraceyPerm block) where
  eta_nonneg := by
    simpa only [envelope, tower] using
      ActualWreathCompressionTower.envelope_eta_nonneg
        (tower hTraceyHalf hTraceyLog hTraceyPerm block)
  seedDegree_two_le := by
    rw [envelope, ActualWreathCompressionTower.envelope_v]
    simpa using block.degrees_ge_two.2
  margin := by
    simpa only [envelope, tower, trace, capacity] using S.margin
  coefficient_bound := by
    intro b
    simpa only [envelope, tower, trace, capacity] using S.coefficient_bound b

/-- **Imprimitive affine-component transfer.**  The component-native source
is transported through the actual block system to one accepted source for
the original ambient action.  The complete normal-axis sum, original action
weight, extension/transgression fibres and the later continuation all remain
inside the complete-source certificate. -/
noncomputable def toAmbientSource :
    PreE7RankTailSourceOrYonedaTopData w U :=
  RelativeCompleteSourceEnvelope.toRankTailSourceOrYonedaTopOfMargin
    .acert (envelope hTraceyHalf hTraceyLog hTraceyPerm block)
      (preE7Margin hTraceyHalf hTraceyLog hTraceyPerm block P S)

end ComponentSource

/-- Function spelling used by the primitive-catalogue consumer assembly. -/
noncomputable def imprimitiveAffineComponentTransfer
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (S : ComponentSource hTraceyHalf hTraceyLog hTraceyPerm block P) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  ComponentSource.toAmbientSource hTraceyHalf hTraceyLog hTraceyPerm block P S

/-- Correct construction target for every imprimitive affine component.
The generic capacity alternative alone is false in the small exceptional
block cells, so the target also permits an already integrated ambient owner.
No literature interface is allowed to return this project-owned sum. -/
structure PreE7PrimitiveAffineImprimitiveComponentSourceData
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) : Type 1 where
  source : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    (P : PrimitiveAffineProfile block.Component block.Fibre) →
    ComponentSource hTraceyHalf hTraceyLog hTraceyPerm block P ⊕
      PreE7RankTailSourceOrYonedaTopData w U

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
