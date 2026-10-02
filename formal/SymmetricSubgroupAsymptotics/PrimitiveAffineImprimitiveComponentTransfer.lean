import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveBlockTransfer
import SymmetricSubgroupAsymptotics.ActualWreathCompressionTowerExistence
import SymmetricSubgroupAsymptotics.RelativeCompleteSourcePreE7Bridge

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
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) :
    ActualWreathCompressionState block.Top block.Points := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp
      (show 1 < Nat.card block.Fibre by
        have := block.degrees_ge_two.1
        omega)
  exact
    { A := preE7NonPairAction w U
      D := block.Component
      groupA := inferInstance
      finiteA := inferInstance
      groupD := inferInstance
      finiteD := inferInstance
      rho := ambientEmbedding block
      rho_injective := ambientEmbedding_injective block
      fullComponent := ActualBlockWreathEmbedding.fullComponent
        block.map block.map_equivariant block.base }

/-- The group-native source carried by an affine primitive component.  Its
capacity field is evaluated on all quotient states of the same real block
system.  The remaining two fields are precisely the mathematical estimates
on that constructed envelope: the affine capacity margin and its finite
coefficient bound.  The growing-transfer parameters are derived later and
are not included as assumptions. -/
structure ComponentSource
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (_P : PrimitiveAffineProfile block.Component block.Fibre) : Type 1 where
  capacity : ActualWreathElementaryCapacityInput
    (Q := block.Top) (I := block.Points)
  margin :
    let tower := ActualWreathCompressionTower.canonicalOfCapacity
      capacity (initialState block)
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - tower.envelope.v) / 8 - tower.envelope.eta
  coefficient_bound :
    let tower := ActualWreathCompressionTower.canonicalOfCapacity
      capacity (initialState block)
    ∀ b, tower.envelope.coefficient b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace ComponentSource

variable
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  (S : ComponentSource block P)

/-- The literal local-chief tower selected by the component source. -/
noncomputable def tower :
    ActualWreathCompressionTower (initialState block) :=
  ActualWreathCompressionTower.canonicalOfCapacity S.capacity
    (initialState block)

/-- Complete quotient-weight transfer from the original ambient group to
the faithful action of the actual top on the original blocks. -/
noncomputable def envelope :
    RelativeCompleteSourceEnvelope (preE7NonPairAction w U) :=
  S.tower block P |>.envelope

/-- The two component estimates, together with the structural facts proved
by the actual tower, give the exact numerical margin record expected by the
pre-E7 transfer. -/
noncomputable def preE7Margin :
    RelativeCompleteSourceEnvelope.PreE7Margin (S.envelope block P) where
  eta_nonneg := by
    simpa only [envelope, tower] using
      ActualWreathCompressionTower.envelope_eta_nonneg (S.tower block P)
  seedDegree_two_le := by
    rw [envelope, ActualWreathCompressionTower.envelope_v]
    simpa using block.degrees_ge_two.2
  margin := by
    simpa only [envelope, tower] using S.margin
  coefficient_bound := by
    intro b
    simpa only [envelope, tower] using S.coefficient_bound b

/-- **Imprimitive affine-component transfer.**  The component-native source
is transported through the actual block system to one accepted source for
the original ambient action.  The complete normal-axis sum, original action
weight, extension/transgression fibres and the later continuation all remain
inside the complete-source certificate. -/
noncomputable def toAmbientSource :
    PreE7RankTailSourceOrYonedaTopData w U :=
  RelativeCompleteSourceEnvelope.toRankTailSourceOrYonedaTopOfMargin
    .acert (S.envelope block P) (preE7Margin block P S)

end ComponentSource

/-- Function spelling used by the primitive-catalogue consumer assembly. -/
noncomputable def imprimitiveAffineComponentTransfer
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (S : ComponentSource block P) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  S.toAmbientSource block P

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
