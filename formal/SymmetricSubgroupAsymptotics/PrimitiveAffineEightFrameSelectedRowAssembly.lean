import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameInducedRowMatch
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameOrderTwentyOneLocalCatalogue

/-!
# Assembly boundary for the selected order-168 eight-frame row

The selected row with zero-based index `28` has a transitive top of order
`168`.  Its order-`21` point stabilizer has a canonical quotient of order
three by a Sylow-seven subgroup, so no generated local target or kernel
field remains.  This file records the remaining exact finite checks and
assembles them into the sparse matched-row interface.

The only row-specific representation check retained here is an injective
intertwiner from the literal induced frame to the emitted matrix module.
Together with equality of dimensions this is automatically a representation
equivalence.  Thus the generated certificate does not have to construct an
inverse coordinate map.
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

local instance selectedRowAssemblyPrimeFact : Fact P.p.Prime :=
  (chart block P).primeFact

namespace DegreeFourZeroCoreEightSparseEmbeddedRow

/-- An embedded sparse row whose model has the same dimension as the full
literal frame is in fact a matched row.  This is the exact upgrade needed by
the emitted sixteen-dimensional eight-frame records. -/
noncomputable def toMatchedOfFinrankEq
    (C : DegreeFourZeroCoreEightSparseEmbeddedRow block P)
    (hdim :
      Module.finrank (ZMod P.p)
          (block.Points → (chart block P).V) =
        Module.finrank (ZMod P.p) C.ModelModule) :
    DegreeFourZeroCoreEightSparseMatchedRow block P where
  ModelGroup := C.ModelGroup
  ModelModule := C.ModelModule
  representation := C.representation
  groupEquiv := C.groupEquiv
  fullFrameEquiv := C.fullFrameEmbedding.ofBijective ⟨
    C.fullFrameEmbedding_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      C.fullFrameEmbedding_injective⟩
  classCount := C.classCount
  representative := C.representative
  conjugacyCover := C.conjugacyCover
  TopIndex := C.TopIndex
  AmbientIndex := C.AmbientIndex
  GeneratorIndex := C.GeneratorIndex
  ambient := C.ambient
  stateGenerators := C.stateGenerators
  top := C.top
  moduleRegistry := C.moduleRegistry

end DegreeFourZeroCoreEightSparseEmbeddedRow

/-- The full degree-four translation frame over eight blocks has dimension
sixteen.  This removes the actual-action side of the dimension check from
the generated row: the emitter only has to check that its coordinate module
has the advertised dimension. -/
theorem degreeFourEightFullFrame_finrank_eq_sixteen
    (hr : Nat.card block.Fibre = 4)
    (hs : Nat.card block.Points = 8) :
    Module.finrank (ZMod P.p)
      (block.Points → (chart block P).V) = 16 := by
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree₀ : Nat.card block.Fibre = P.p ^ C.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (origin block)
  have hdegree : 4 = P.p ^ C.d := hr.symm.trans hdegree₀
  have hpd := prime_pow_positive_injective (d := C.d) (e := 2)
    P.p_prime Nat.prime_two C.d_pos (by norm_num)
    (hdegree.symm.trans (by norm_num))
  have hdim : Module.finrank (ZMod P.p) C.V = 2 := by
    simpa only [PrimitiveAffineProfile.ElementaryChart.d] using hpd.2
  change Module.finrank (ZMod P.p) (block.Points → C.V) = 16
  simp only [Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Nat.nsmul_eq_mul, Fintype.card_eq_nat_card,
    hs, hdim]

/-- Exact data still required after the selected order-168 top has been
emitted.  The point is fixed to the inverse image of row point zero.  The
order-three local comparison is reconstructed canonically from the literal
top and is not a field of this structure.

Every field after `inducedEmbedding_injective` is a finite registry already
described by the selected certificate schema.  `model_finrank_eq_sixteen`
is the small coordinate check which upgrades the sufficient embedded row to
the stronger matched-row interface. -/
structure DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    (topMatch : DegreeFourZeroCoreEightLiteralTopMatch
      block ModelGroup)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) : Type 1 where
  modelGroup_card : Nat.card ModelGroup = 168
  ModelModule : Type
  [modelAddCommGroup : AddCommGroup ModelModule]
  [modelModule : Module (ZMod P.p) ModelModule]
  [modelFiniteDimensional : FiniteDimensional
    (ZMod P.p) ModelModule]
  [modelFinite : Finite ModelModule]
  representation : Representation
    (ZMod P.p) ModelGroup ModelModule
  inducedEmbedding :
    (Representation.ind
      (fullFrameInducedStabilizer block P
        (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
          (block := block) topMatch (0 : Fin 8))).subtype
      (fullFrameInducedLocalRepresentation block P
        (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
          (block := block) topMatch (0 : Fin 8)))).IntertwiningMap
      (representation.comp
        (DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
          (block := block) (P := P) topMatch hr hD).toMonoidHom)
  inducedEmbedding_injective : Function.Injective inducedEmbedding
  model_finrank_eq_sixteen :
    Module.finrank (ZMod P.p) ModelModule = 16
  classCount : ℕ
  representative : Fin classCount → ModelGroup
  conjugacyCover : FiniteConjugacyCardinalCover representative
  TopIndex : Type
  [topIndexFinite : Finite TopIndex]
  AmbientIndex : Type
  GeneratorIndex : Type
  ambient : AmbientIndex → ModelGroup
  stateGenerators : TopIndex → GeneratorIndex → ModelGroup
  top : FiniteTopRelativeBinaryRankWordRegistry
    (rank := 2) conjugacyCover ambient stateGenerators
  moduleRegistry : FiniteFrameModuleCyclicOrbitDisplacementRegistry
    representation 2

attribute [instance]
  DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow.modelAddCommGroup
  DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow.modelModule
  DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow.modelFiniteDimensional
  DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow.modelFinite
  DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow.topIndexFinite

namespace DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow

/-- The local compatibility square is forced generically by the exact top
order.  In particular, it is not an additional generated hypothesis. -/
noncomputable def pointedLocalMatch
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    {topMatch : DegreeFourZeroCoreEightLiteralTopMatch
      block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    (C : DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow
      block P topMatch hr hD) :
    DegreeFourZeroCoreEightPointedLocalMatch
      block P topMatch hr hD (0 : Fin 8) :=
  DegreeEightLiteralLocalRowCatalogue.selectActualCanonicalOrderOneSixtyEight
    block P topMatch hr hD C.modelGroup_card

/-- Package the emitted induced-coordinate check in the generic row-match
interface. -/
noncomputable def inducedRowMatch
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    {topMatch : DegreeFourZeroCoreEightLiteralTopMatch
      block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    (C : DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow
      block P topMatch hr hD) :
    DegreeFourZeroCoreEightInducedRowMatch
      block P ModelGroup C.ModelModule C.representation
        (DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
          (block := block) (P := P) topMatch hr hD) where
  point := DegreeFourZeroCoreEightLiteralTopMatch.pointOver
    (block := block) topMatch (0 : Fin 8)
  inducedEmbedding := C.inducedEmbedding
  inducedEmbedding_injective := C.inducedEmbedding_injective

/-- The selected row first gives the sufficient embedded-row boundary. -/
noncomputable def toSparseEmbeddedRow
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    {topMatch : DegreeFourZeroCoreEightLiteralTopMatch
      block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    (C : DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow
      block P topMatch hr hD) :
    DegreeFourZeroCoreEightSparseEmbeddedRow block P := by
  let groupEquiv :=
    DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
      (block := block) (P := P) topMatch hr hD
  let inducedMatch := C.inducedRowMatch block P
  let frameMatch :=
    DegreeFourZeroCoreEightInducedRowMatch.toLiteralFrameMatch
      block P C.representation groupEquiv inducedMatch
  exact DegreeFourZeroCoreEightLiteralFrameMatch.toSparseEmbeddedRow
    block P C.representation groupEquiv frameMatch
      C.representative C.conjugacyCover C.ambient C.stateGenerators
      C.top C.moduleRegistry

/-- The dimension equality upgrades the selected row to the exact sparse
matched boundary requested by the finite-frame catalogue. -/
noncomputable def toSparseMatchedRow
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    {topMatch : DegreeFourZeroCoreEightLiteralTopMatch
      block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    (C : DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow
      block P topMatch hr hD)
    (hs : Nat.card block.Points = 8) :
    DegreeFourZeroCoreEightSparseMatchedRow block P :=
  (C.toSparseEmbeddedRow block P).toMatchedOfFinrankEq
    block P ((degreeFourEightFullFrame_finrank_eq_sixteen block P hr hs).trans
      C.model_finrank_eq_sixteen.symm)

/-- The selected row already supplies the exact five-slot finite-frame
bound consumed by the structural bridge. -/
noncomputable def toBounds [Finite (elementaryChart block P).V]
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    {topMatch : DegreeFourZeroCoreEightLiteralTopMatch
      block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    (C : DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow
      block P topMatch hr hD)
    (hs : Nat.card block.Points = 8) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 :=
  (C.toSparseMatchedRow block P hs).toBounds block P

end DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow

/-- A selected eight-frame row after the local Schreier calculation has
already been checked.  This is the order-uniform publication boundary: the
model top and its point-stabilizer quotient may have any of the finite
orders in the retained catalogue. -/
structure DegreeFourZeroCoreEightSelectedRow
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    (topMatch : DegreeFourZeroCoreEightLiteralTopMatch
      block ModelGroup)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) : Type 1 where
  ModelModule : Type
  [modelAddCommGroup : AddCommGroup ModelModule]
  [modelModule : Module (ZMod P.p) ModelModule]
  [modelFiniteDimensional : FiniteDimensional
    (ZMod P.p) ModelModule]
  [modelFinite : Finite ModelModule]
  representation : Representation
    (ZMod P.p) ModelGroup ModelModule
  inducedEmbedding :
    (Representation.ind
      (fullFrameInducedStabilizer block P
        (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
          (block := block) topMatch (0 : Fin 8))).subtype
      (fullFrameInducedLocalRepresentation block P
        (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
          (block := block) topMatch (0 : Fin 8)))).IntertwiningMap
      (representation.comp
        (DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
          (block := block) (P := P) topMatch hr hD).toMonoidHom)
  inducedEmbedding_injective : Function.Injective inducedEmbedding
  model_finrank_eq_sixteen :
    Module.finrank (ZMod P.p) ModelModule = 16
  classCount : ℕ
  representative : Fin classCount → ModelGroup
  conjugacyCover : FiniteConjugacyCardinalCover representative
  TopIndex : Type
  [topIndexFinite : Finite TopIndex]
  AmbientIndex : Type
  GeneratorIndex : Type
  ambient : AmbientIndex → ModelGroup
  stateGenerators : TopIndex → GeneratorIndex → ModelGroup
  top : FiniteTopRelativeBinaryRankWordRegistry
    (rank := 2) conjugacyCover ambient stateGenerators
  moduleRegistry : FiniteFrameModuleCyclicOrbitDisplacementRegistry
    representation 2

attribute [instance]
  DegreeFourZeroCoreEightSelectedRow.modelAddCommGroup
  DegreeFourZeroCoreEightSelectedRow.modelModule
  DegreeFourZeroCoreEightSelectedRow.modelFiniteDimensional
  DegreeFourZeroCoreEightSelectedRow.modelFinite
  DegreeFourZeroCoreEightSelectedRow.topIndexFinite

namespace DegreeFourZeroCoreEightSelectedRow

/-- Package the checked induced embedding as the generic row match. -/
noncomputable def inducedRowMatch
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    {topMatch : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    (C : DegreeFourZeroCoreEightSelectedRow block P topMatch hr hD) :
    DegreeFourZeroCoreEightInducedRowMatch
      block P ModelGroup C.ModelModule C.representation
        (DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
          (block := block) (P := P) topMatch hr hD) where
  point := DegreeFourZeroCoreEightLiteralTopMatch.pointOver
    (block := block) topMatch (0 : Fin 8)
  inducedEmbedding := C.inducedEmbedding
  inducedEmbedding_injective := C.inducedEmbedding_injective

/-- Forget the exact coordinate dimension after constructing the literal
frame equivalence. -/
noncomputable def toSparseEmbeddedRow
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    {topMatch : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    (C : DegreeFourZeroCoreEightSelectedRow block P topMatch hr hD) :
    DegreeFourZeroCoreEightSparseEmbeddedRow block P := by
  let groupEquiv :=
    DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
      (block := block) (P := P) topMatch hr hD
  let frameMatch :=
    DegreeFourZeroCoreEightInducedRowMatch.toLiteralFrameMatch
      block P C.representation groupEquiv (C.inducedRowMatch block P)
  exact DegreeFourZeroCoreEightLiteralFrameMatch.toSparseEmbeddedRow
    block P C.representation groupEquiv frameMatch
      C.representative C.conjugacyCover C.ambient C.stateGenerators
      C.top C.moduleRegistry

/-- The checked sixteen-dimensional model is the full degree-four frame. -/
noncomputable def toSparseMatchedRow
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    {topMatch : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    (C : DegreeFourZeroCoreEightSelectedRow block P topMatch hr hD)
    (hs : Nat.card block.Points = 8) :
    DegreeFourZeroCoreEightSparseMatchedRow block P :=
  (C.toSparseEmbeddedRow block P).toMatchedOfFinrankEq
    block P ((degreeFourEightFullFrame_finrank_eq_sixteen block P hr hs).trans
      C.model_finrank_eq_sixteen.symm)

/-- The order-uniform selected row supplies the five-slot capacity bound. -/
noncomputable def toBounds [Finite (elementaryChart block P).V]
    {ModelGroup : Type} [Group ModelGroup] [Finite ModelGroup]
    {topMatch : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    (C : DegreeFourZeroCoreEightSelectedRow block P topMatch hr hD)
    (hs : Nat.card block.Points = 8) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 :=
  (C.toSparseMatchedRow block P hs).toBounds block P

end DegreeFourZeroCoreEightSelectedRow

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
