import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameEmbeddedRow
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameInducedTopNaturality
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameLocalRepresentation
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameLocalRowCatalogue
import SymmetricSubgroupAsymptotics.FiniteTopRelativeBinaryRankWordRegistry

/-!
# Shared data for generated sixteen-frame tables

The Cayley group, point stabilizer, Schreier transversal, normal-state
registry, and top relative-head bound depend only on a transitive top.  The
local quotient, induced representation, and odd-normalizer witness vary by
row.  These structures keep that split explicit so the transport proof is
written once for the whole finite catalogue.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Data shared by every checked row over one literal sixteen-point top. -/
structure GeneratedSixteenTopData : Type 1 where
  ModelGroup : Type
  [modelGroup : Group ModelGroup]
  [modelFinite : Finite ModelGroup]
  literalAction : Subgroup (Equiv.Perm (Fin 16))
  actionModelEquiv : literalAction ≃* ModelGroup
  sourceStabilizer : Subgroup ModelGroup
  [sourceStabilizerMembership : DecidablePred (fun x ↦ x ∈ sourceStabilizer)]
  [sourceStabilizerFintype : Fintype sourceStabilizer]
  sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer literalAction (0 : Fin 16)
  sourceStabilizerEquivLiteral_model : ∀ h : sourceStabilizer,
    actionModelEquiv (sourceStabilizerEquivLiteral h).1 = h.1
  GeneratorIndex : Type
  ambient : GeneratorIndex → ModelGroup
  ambient_full : Subgroup.closure (Set.range ambient) = ⊤
  representative : Fin 16 → ModelGroup
  representative_factor : ∀ x : ModelGroup,
    ∃ h : ModelGroup, h ∈ sourceStabilizer ∧
      ∃ a : Fin 16, x = h * representative a
  next : GeneratorIndex → Fin 16 → Fin 16
  twist : GeneratorIndex → Fin 16 → sourceStabilizer
  representative_mul_generator : ∀ j a,
    representative a * ambient j =
      (twist j a : ModelGroup) * representative (next j a)
  classCount : ℕ
  conjugacyRepresentative : Fin classCount → ModelGroup
  conjugacyCover : FiniteConjugacyCardinalCover conjugacyRepresentative
  TopIndex : Type
  [topIndexFinite : Finite TopIndex]
  NormalGeneratorIndex : Type
  stateGenerators : TopIndex → NormalGeneratorIndex → ModelGroup
  topSlots : ℕ
  topRegistry : FiniteTopRelativeBinaryRankWordRegistry
    (rank := topSlots) conjugacyCover ambient stateGenerators

attribute [instance]
  GeneratedSixteenTopData.modelGroup
  GeneratedSixteenTopData.modelFinite
  GeneratedSixteenTopData.sourceStabilizerMembership
  GeneratedSixteenTopData.sourceStabilizerFintype
  GeneratedSixteenTopData.topIndexFinite

namespace GeneratedSixteenTopData

/-- Recover the literal point stabilizer from its checked fixing predicate. -/
def sourceStabilizerEquivLiteralOfFixingPredicate
    {ModelGroup : Type} [Group ModelGroup]
    (literalAction : Subgroup (Equiv.Perm (Fin 16)))
    (actionModelEquiv : literalAction ≃* ModelGroup)
    (sourceStabilizer : Subgroup ModelGroup)
    (fixes_zero : ∀ x : ModelGroup,
      x ∈ sourceStabilizer ↔
        (((actionModelEquiv.symm x : literalAction) :
          Equiv.Perm (Fin 16)) (0 : Fin 16) = 0)) :
    sourceStabilizer ≃*
      MulAction.stabilizer literalAction (0 : Fin 16) where
  toFun x := ⟨actionModelEquiv.symm x.1,
    (fixes_zero x.1).mp x.2⟩
  invFun x := ⟨actionModelEquiv x.1,
    (fixes_zero (actionModelEquiv x.1)).mpr (by
      rw [actionModelEquiv.symm_apply_apply]
      exact x.2)⟩
  left_inv x := by
    apply Subtype.ext
    exact actionModelEquiv.apply_symm_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact actionModelEquiv.symm_apply_apply x.1
  map_mul' x y := by
    apply Subtype.ext
    exact actionModelEquiv.symm.map_mul x.1 y.1

theorem sourceStabilizerEquivLiteralOfFixingPredicate_model
    {ModelGroup : Type} [Group ModelGroup]
    (literalAction : Subgroup (Equiv.Perm (Fin 16)))
    (actionModelEquiv : literalAction ≃* ModelGroup)
    (sourceStabilizer : Subgroup ModelGroup)
    (fixes_zero : ∀ x : ModelGroup,
      x ∈ sourceStabilizer ↔
        (((actionModelEquiv.symm x : literalAction) :
          Equiv.Perm (Fin 16)) (0 : Fin 16) = 0))
    (h : sourceStabilizer) :
    actionModelEquiv
        ((sourceStabilizerEquivLiteralOfFixingPredicate literalAction
          actionModelEquiv sourceStabilizer fixes_zero h).1) = h.1 :=
  actionModelEquiv.apply_symm_apply h.1

/-- Bind the stored top to an arbitrary literal zero-core block action. -/
def literalTopMatch
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (T : GeneratedSixteenTopData)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (pointEquiv : block.Points ≃ Fin 16)
    (conjugator : Equiv.Perm (Fin 16))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        T.literalAction) :
    DegreeFourZeroCoreSixteenLiteralTopMatch block T.ModelGroup where
  literalAction := T.literalAction
  actionModelEquiv := T.actionModelEquiv
  pointEquiv := pointEquiv
  conjugator := conjugator
  conjugated := hconjugated

end GeneratedSixteenTopData

/-- Row-varying data over a shared sixteen-point top. -/
structure GeneratedSixteenRowData (T : GeneratedSixteenTopData) : Type 1 where
  LocalTarget : Type
  [localTargetGroup : Group LocalTarget]
  [localTargetFinite : Finite LocalTarget]
  sourceLocalMap : T.sourceStabilizer →* LocalTarget
  sourceLocalMap_surjective : Function.Surjective sourceLocalMap
  local_card : Nat.card LocalTarget = 3 ∨ Nat.card LocalTarget = 6
  localRepresentation :
    Representation (ZMod 2) LocalTarget (Fin 2 → ZMod 2)
  localRepresentation_injective : Function.Injective localRepresentation
  modelRepresentation :
    Representation (ZMod 2) T.ModelGroup (Fin 32 → ZMod 2)
  modelRepresentation_generator_formula : ∀
      (j : T.GeneratorIndex) (v : Fin 32 → ZMod 2)
      (a : Fin 16) (i : Fin 2),
    modelRepresentation (T.ambient j) v
        (CoinducedLeadingCoordinates.label a i) =
      localRepresentation (sourceLocalMap (T.twist j a))
        (fun q ↦ v (CoinducedLeadingCoordinates.label (T.next j a) q)) i
  fixedWitness : FiniteFrameOddNormalizerWitness modelRepresentation
  slot_sum_le : T.topSlots + fixedWitness.dimension ≤ 10

attribute [instance]
  GeneratedSixteenRowData.localTargetGroup
  GeneratedSixteenRowData.localTargetFinite

namespace GeneratedSixteenRowData

def literalLocalMap (T : GeneratedSixteenTopData)
    (R : GeneratedSixteenRowData T) :
    MulAction.stabilizer T.literalAction (0 : Fin 16) →* R.LocalTarget :=
  R.sourceLocalMap.comp T.sourceStabilizerEquivLiteral.symm.toMonoidHom

theorem literalLocalMap_surjective (T : GeneratedSixteenTopData)
    (R : GeneratedSixteenRowData T) :
    Function.Surjective (R.literalLocalMap T) :=
  R.sourceLocalMap_surjective.comp
    T.sourceStabilizerEquivLiteral.symm.surjective

noncomputable def literalLocalRow (T : GeneratedSixteenTopData)
    (R : GeneratedSixteenRowData T) :
    DegreeSixteenLiteralLocalRow T.literalAction where
  ModelLocalGroup := R.LocalTarget
  literalLocalMap := R.literalLocalMap T
  literalLocalMap_surjective := R.literalLocalMap_surjective T
  local_card := R.local_card

end GeneratedSixteenRowData

/-- Complete dependent catalogue of eligible local quotients over one top. -/
structure GeneratedSixteenTopTable (T : GeneratedSixteenTopData) : Type 1 where
  Row : Type
  data : Row → GeneratedSixteenRowData T
  complete : ∀ (L : Type) [Group L] [Finite L]
      (f : MulAction.stabilizer T.literalAction (0 : Fin 16) →* L),
    Function.Surjective f →
    (Nat.card L = 3 ∨ (Nat.card L = 6 ∧ ¬ IsMulCommutative L)) →
    ∃ r : Row, ∃ e : L ≃* (data r).LocalTarget,
      e.toMonoidHom.comp f = (data r).literalLocalMap T

namespace GeneratedSixteenTopTable

noncomputable def localCatalogue (T : GeneratedSixteenTopData)
    (C : GeneratedSixteenTopTable T) :
    DegreeSixteenLiteralLocalRowCatalogue T.literalAction where
  Row := C.Row
  row := fun r ↦ (C.data r).literalLocalRow T
  complete := C.complete

end GeneratedSixteenTopTable

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
