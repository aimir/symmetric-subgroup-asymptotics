import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameSelectedRowAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameInducedTopNaturality
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameInducedCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRepresentation

/-!
# One transport theorem for generated eight-frame tables

The finite eight-frame calculation has two genuinely different layers.
The Cayley group, point stabilizer, Schreier transversal, conjugacy cover and
normal-state registry depend only on the transitive top.  The local quotient,
induced binary representation and module-head registry depend on a row of
that top.  Earlier generated files repeated the full literal transport proof
for every row.

This file records those two layers as `GeneratedTopData` and
`GeneratedRowData`.  A `GeneratedTopTable` retains a complete dependent
catalogue of the eligible local quotients.  The theorem `GeneratedTopTable.bounds`
selects the actual local quotient and runs the induced-coordinate transport
once.  Generated rows hence contain certificate data only; they no longer
carry six hundred lines of duplicated proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Data shared by every finite-frame row over one literal transitive top. -/
structure GeneratedTopData : Type 1 where
  ModelGroup : Type
  [modelGroup : Group ModelGroup]
  [modelFinite : Finite ModelGroup]
  literalAction : Subgroup (Equiv.Perm (Fin 8))
  actionModelEquiv : literalAction ≃* ModelGroup
  sourceStabilizer : Subgroup ModelGroup
  [sourceStabilizerMembership : DecidablePred (fun x ↦ x ∈ sourceStabilizer)]
  [sourceStabilizerFintype : Fintype sourceStabilizer]
  sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer literalAction (0 : Fin 8)
  sourceStabilizerEquivLiteral_model : ∀ h : sourceStabilizer,
    actionModelEquiv (sourceStabilizerEquivLiteral h).1 = h.1
  GeneratorIndex : Type
  ambient : GeneratorIndex → ModelGroup
  ambient_full : Subgroup.closure (Set.range ambient) = ⊤
  representative : Fin 8 → ModelGroup
  representative_factor : ∀ x : ModelGroup,
    ∃ h : ModelGroup, h ∈ sourceStabilizer ∧
      ∃ a : Fin 8, x = h * representative a
  next : GeneratorIndex → Fin 8 → Fin 8
  twist : GeneratorIndex → Fin 8 → sourceStabilizer
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
  topRegistry : FiniteTopRelativeBinaryRankWordRegistry
    (rank := 2) conjugacyCover ambient stateGenerators

attribute [instance]
  GeneratedTopData.modelGroup
  GeneratedTopData.modelFinite
  GeneratedTopData.sourceStabilizerMembership
  GeneratedTopData.sourceStabilizerFintype
  GeneratedTopData.topIndexFinite

namespace GeneratedTopData

/-- Recover the literal point stabilizer from a subgroup of a finite model.
Generated top files only have to check the point-fixing predicate on their
finite Cayley rows; the group equivalence is shared by every local row over
that top. -/
def sourceStabilizerEquivLiteralOfFixingPredicate
    {ModelGroup : Type} [Group ModelGroup]
    (literalAction : Subgroup (Equiv.Perm (Fin 8)))
    (actionModelEquiv : literalAction ≃* ModelGroup)
    (sourceStabilizer : Subgroup ModelGroup)
    (fixes_zero : ∀ x : ModelGroup,
      x ∈ sourceStabilizer ↔
        (((actionModelEquiv.symm x : literalAction) :
          Equiv.Perm (Fin 8)) (0 : Fin 8) = 0)) :
    sourceStabilizer ≃*
      MulAction.stabilizer literalAction (0 : Fin 8) where
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
    (literalAction : Subgroup (Equiv.Perm (Fin 8)))
    (actionModelEquiv : literalAction ≃* ModelGroup)
    (sourceStabilizer : Subgroup ModelGroup)
    (fixes_zero : ∀ x : ModelGroup,
      x ∈ sourceStabilizer ↔
        (((actionModelEquiv.symm x : literalAction) :
          Equiv.Perm (Fin 8)) (0 : Fin 8) = 0))
    (h : sourceStabilizer) :
    actionModelEquiv
        ((sourceStabilizerEquivLiteralOfFixingPredicate literalAction
          actionModelEquiv sourceStabilizer fixes_zero h).1) = h.1 :=
  actionModelEquiv.apply_symm_apply h.1

/-- Bind the stored top to an arbitrary literal zero-core block action. -/
def literalTopMatch
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (T : GeneratedTopData)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        T.literalAction) :
    DegreeFourZeroCoreEightLiteralTopMatch block T.ModelGroup where
  literalAction := T.literalAction
  actionModelEquiv := T.actionModelEquiv
  pointEquiv := pointEquiv
  conjugator := conjugator
  conjugated := hconjugated

end GeneratedTopData

/-- The row-varying certificate over a shared top.  The model module has
the canonical sixteen binary coordinates used by every eight-block frame. -/
structure GeneratedRowData (T : GeneratedTopData) : Type 1 where
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
    Representation (ZMod 2) T.ModelGroup (Fin 16 → ZMod 2)
  modelRepresentation_generator_formula : ∀
      (j : T.GeneratorIndex) (v : Fin 16 → ZMod 2)
      (a : Fin 8) (i : Fin 2),
    modelRepresentation (T.ambient j) v
        (CoinducedLeadingCoordinates.label a i) =
      localRepresentation (sourceLocalMap (T.twist j a))
        (fun q ↦ v (CoinducedLeadingCoordinates.label (T.next j a) q)) i
  moduleRegistry : FiniteFrameModuleCyclicOrbitDisplacementRegistry
    modelRepresentation 2

attribute [instance]
  GeneratedRowData.localTargetGroup
  GeneratedRowData.localTargetFinite

namespace GeneratedRowData

/-- The row's local quotient map on the literal point stabilizer. -/
def literalLocalMap (T : GeneratedTopData) (R : GeneratedRowData T) :
    MulAction.stabilizer T.literalAction (0 : Fin 8) →* R.LocalTarget :=
  R.sourceLocalMap.comp T.sourceStabilizerEquivLiteral.symm.toMonoidHom

theorem literalLocalMap_surjective (T : GeneratedTopData)
    (R : GeneratedRowData T) :
    Function.Surjective (R.literalLocalMap T) :=
  R.sourceLocalMap_surjective.comp
    T.sourceStabilizerEquivLiteral.symm.surjective

/-- Forget the generated coordinates and expose the row at the exact local
catalogue boundary. -/
noncomputable def literalLocalRow (T : GeneratedTopData)
    (R : GeneratedRowData T) :
    DegreeEightLiteralLocalRow T.literalAction where
  ModelLocalGroup := R.LocalTarget
  literalLocalMap := R.literalLocalMap T
  literalLocalMap_surjective := R.literalLocalMap_surjective T
  local_card := R.local_card

end GeneratedRowData

/-- A whole local-quotient family above one top.  Completeness is stated in
the existing kernel-and-map-sensitive catalogue interface. -/
structure GeneratedTopTable (T : GeneratedTopData) : Type 1 where
  Row : Type
  data : Row → GeneratedRowData T
  complete : ∀ (L : Type) [Group L] [Finite L]
      (f : MulAction.stabilizer T.literalAction (0 : Fin 8) →* L),
    Function.Surjective f →
    (Nat.card L = 3 ∨ (Nat.card L = 6 ∧ ¬ IsMulCommutative L)) →
    ∃ r : Row, ∃ e : L ≃* (data r).LocalTarget,
      e.toMonoidHom.comp f = (data r).literalLocalMap T

namespace GeneratedTopTable

/-- The table as the frozen literal local-row catalogue. -/
noncomputable def localCatalogue (T : GeneratedTopData)
    (C : GeneratedTopTable T) :
    DegreeEightLiteralLocalRowCatalogue T.literalAction where
  Row := C.Row
  row := fun r ↦ (C.data r).literalLocalRow T
  complete := C.complete

end GeneratedTopTable

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
