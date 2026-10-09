import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFramePointedTopMatch
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameFullFrameInduced

/-!
# Naturality of the induced point stabilizer under a literal top match

The finite sixteen-frame importer uses the stabilizer inside the actual
zero-core quotient, while a catalogue row stores the stabilizer inside its
literal permutation top.  These are the same subgroup after the exact top
equivalence.  This file records that restriction and the corresponding
local-map square once, independently of any generated row.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
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

/-- Restrict the exact zero-core top equivalence to the two displayed point
stabilizers. -/
noncomputable def fullFrameInducedStabilizerEquivLiteral
    {ModelGroup : Type} [Group ModelGroup]
    (M : DegreeFourZeroCoreSixteenLiteralTopMatch block ModelGroup)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (literalPoint : Fin 16) :
    fullFrameInducedStabilizer block P
        (DegreeFourZeroCoreSixteenLiteralTopMatch.pointOver
          (block := block) M literalPoint) ≃*
      MulAction.stabilizer M.literalAction literalPoint :=
  (degreeFourZeroCoreTopStabilizerEquiv block P hr hD
      (DegreeFourZeroCoreSixteenLiteralTopMatch.pointOver
        (block := block) M literalPoint)).trans
    (DegreeFourZeroCoreSixteenLiteralTopMatch.stabilizerEquiv
      (block := block) M literalPoint)

/-- The restricted stabilizer equivalence is the restriction of the full
group equivalence used by the emitted representation. -/
theorem groupEquiv_stabilizer
    {ModelGroup : Type} [Group ModelGroup]
    (M : DegreeFourZeroCoreSixteenLiteralTopMatch block ModelGroup)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (literalPoint : Fin 16)
    (x : fullFrameInducedStabilizer block P
      (DegreeFourZeroCoreSixteenLiteralTopMatch.pointOver
        (block := block) M literalPoint)) :
    DegreeFourZeroCoreSixteenLiteralTopMatch.groupEquiv
        (block := block) (P := P) M hr hD x.1 =
      M.actionModelEquiv
        ((fullFrameInducedStabilizerEquivLiteral
          block P M hr hD literalPoint x).1) := by
  rfl

/-- The pointed compatibility square remains exact on the actual induced
stabilizer.  Thus generated Schreier twists may be evaluated by the stored
literal local map. -/
theorem pointedLocalMatch_actual_component
    {ModelGroup : Type} [Group ModelGroup]
    {M : DegreeFourZeroCoreSixteenLiteralTopMatch block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    {literalPoint : Fin 16}
    (L : DegreeFourZeroCoreSixteenPointedLocalMatch
      block P M hr hD literalPoint)
    (x : fullFrameInducedStabilizer block P
      (DegreeFourZeroCoreSixteenLiteralTopMatch.pointOver
        (block := block) M literalPoint)) :
    L.targetEquiv (binaryAffineStabilizerComponent block P
        (DegreeFourZeroCoreSixteenLiteralTopMatch.pointOver
          (block := block) M literalPoint) x) =
      L.literalLocalMap
        (fullFrameInducedStabilizerEquivLiteral
          block P M hr hD literalPoint x) := by
  let E := degreeFourZeroCoreTopStabilizerEquiv block P hr hD
    (DegreeFourZeroCoreSixteenLiteralTopMatch.pointOver
      (block := block) M literalPoint)
  let F := DegreeFourZeroCoreSixteenLiteralTopMatch.stabilizerEquiv
    (block := block) M literalPoint
  have hcancel : E.symm (F.symm ((E.trans F) x)) = x := by
    rw [MulEquiv.trans_apply, F.symm_apply_apply, E.symm_apply_apply]
  have h := DFunLike.congr_fun L.compatible
    (fullFrameInducedStabilizerEquivLiteral
      block P M hr hD literalPoint x)
  change L.targetEquiv
      (binaryAffineStabilizerComponent block P
        (DegreeFourZeroCoreSixteenLiteralTopMatch.pointOver
          (block := block) M literalPoint)
        (E.symm (F.symm ((E.trans F) x)))) =
    L.literalLocalMap ((E.trans F) x) at h
  rw [hcancel] at h
  simpa [DegreeFourZeroCoreSixteenLiteralTopMatch.transportedLocalMap,
    fullFrameInducedStabilizerEquivLiteral,
    degreeFourZeroCoreTopStabilizerLocalMap,
    E, F, MulEquiv.trans_apply] using h

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
