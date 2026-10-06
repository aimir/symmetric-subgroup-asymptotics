import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreTopEquiv
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameSparseEmbeddedCatalogue

/-!
# Literal binding obligations for an eight-block frame row

This file separates the published degree-eight top classification from the
kernel-checked frame computation.  The published input may only select one
literal permutation top.  The stabilizer kernel, local epimorphism, linear
frame and sparse registries remain checked data.

For a selected row, the handwritten transport has two parts:

1. relabel and ambient-conjugate the actual block top to the row's literal
   degree-eight permutation subgroup; this file constructs the resulting
   exact abstract-group equivalence; and
2. give an injective intertwiner from the actual full translation frame to
   the checked row representation.  This second field is the precise place
   where the stored stabilizer kernel, local epimorphism and frame matrices
   must be matched.  It cannot be supplied by a top-only classification.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The published finite degree-eight correspondence, parameterized by the
literal top family emitted by the certificate generator.  It says only that
every transitive non-2 degree-eight action is ambient-conjugate to a listed
top. -/
def PublishedDegreeEightNonbinaryTopClassification
    (tops : Fin 24 → Subgroup (Equiv.Perm (Fin 8))) : Prop :=
  ∀ (T : Subgroup (Equiv.Perm (Fin 8))),
    PermutationSubgroupTransitive T →
    ¬ IsPGroup 2 T →
    ∃ i : Fin 24, ∃ g : Equiv.Perm (Fin 8),
      MulAut.conj g • T = tops i

/-- One literal top together with the executable group used by its generated
finite certificates. -/
structure DegreeEightLiteralTopModel : Type 1 where
  ModelGroup : Type
  [modelGroup : Group ModelGroup]
  [modelFinite : Finite ModelGroup]
  literalAction : Subgroup (Equiv.Perm (Fin 8))
  actionModelEquiv : literalAction ≃* ModelGroup

attribute [instance]
  DegreeEightLiteralTopModel.modelGroup
  DegreeEightLiteralTopModel.modelFinite

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance literalBindingPrimeFact : Fact P.p.Prime :=
  (chart block P).primeFact

/-- The local affine complement has order three or six and is a quotient of
a point stabilizer in the zero-core top.  Hence that top cannot be a
2-group.  This is the structural fact which makes the published nonbinary
degree-eight classifier applicable; it is not a catalogue assumption. -/
theorem degreeFourZeroCoreTop_not_isPGroup_two
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    ¬ IsPGroup 2 block.Top := by
  intro htop
  let i : block.Points := Classical.choice
    (Finite.card_pos_iff.mp (by
      have h := block.degrees_ge_two.2
      omega))
  have hquotient : IsPGroup 2 (DegreeFourComplementQuotient block P) :=
    htop.of_equiv (degreeFourZeroCoreTopEquiv block P hr hD).symm
  have hstabilizer : IsPGroup 2
      (binaryAffineQuotientTopStabilizer block P i) :=
    hquotient.to_subgroup _
  have hlocal : IsPGroup 2 (LocalQuotient block P) :=
    hstabilizer.of_surjective
      (binaryAffineStabilizerComponent block P i)
      (binaryAffineStabilizerComponent_surjective block P i)
  obtain ⟨n, hn⟩ := hlocal.exists_card_eq
  have hlocalCard : Nat.card (LocalQuotient block P) = 3 ∨
      Nat.card (LocalQuotient block P) = 6 := by
    rw [localQuotient_card_eq_complement block P]
    exact degreeFour_complement_card_eq_three_or_six block P hr
  rcases hlocalCard with h3 | h6
  · rw [h3] at hn
    cases n with
    | zero => norm_num at hn
    | succ n =>
        rw [pow_succ] at hn
        omega
  · rw [h6] at hn
    cases n with
    | zero => norm_num at hn
    | succ n =>
        rw [pow_succ] at hn
        have hpow : 3 = 2 ^ n := by omega
        cases n with
        | zero => norm_num at hpow
        | succ n =>
            rw [pow_succ] at hpow
            omega

/-- Exact top-only identification of the actual zero-core quotient with a
finite row.  `actionModelEquiv` is normally the inverse of the generated
Cayley row's `originalEquiv`. -/
structure DegreeFourZeroCoreEightLiteralTopMatch
    (ModelGroup : Type) [Group ModelGroup] : Type 1 where
  literalAction : Subgroup (Equiv.Perm (Fin 8))
  actionModelEquiv : literalAction ≃* ModelGroup
  pointEquiv : block.Points ≃ Fin 8
  conjugator : Equiv.Perm (Fin 8)
  conjugated :
    MulAut.conj conjugator •
      relabelSubgroup pointEquiv block.Top = literalAction

namespace DegreeFourZeroCoreEightLiteralTopMatch

/-- Compose the zero-core quotient-to-top map, point relabelling, ambient
conjugacy and the generated Cayley equivalence.  No stabilizer or module
claim is used here. -/
noncomputable def groupEquiv
    {ModelGroup : Type} [Group ModelGroup]
    (M : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    DegreeFourComplementQuotient block P ≃* ModelGroup :=
  (degreeFourZeroCoreTopEquiv block P hr hD).trans
    ((M.pointEquiv.permCongrHom.subgroupMap block.Top).trans
      ((actionConjugacyEquiv M.conjugator M.conjugated).trans
        M.actionModelEquiv))

end DegreeFourZeroCoreEightLiteralTopMatch

/-- Apply the published top-only classification to the actual block top.
Everything after row selection is retained as a separate checked
obligation. -/
noncomputable def degreeFourZeroCoreLiteralTopMatch_of_published
    (models : Fin 24 → DegreeEightLiteralTopModel)
    (published : PublishedDegreeEightNonbinaryTopClassification
      (fun i => (models i).literalAction))
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8) :
    Σ i : Fin 24,
      DegreeFourZeroCoreEightLiteralTopMatch
        block (models i).ModelGroup := by
  let pointEquiv : block.Points ≃ Fin 8 := Finite.equivFinOfCardEq hs
  let T := relabelSubgroup pointEquiv block.Top
  have htopTransitive : PermutationSubgroupTransitive block.Top := by
    letI : MulAction.IsPretransitive block.Top block.Points :=
      block.top_pretransitive
    intro x y
    obtain ⟨g, hxy⟩ := MulAction.exists_smul_eq block.Top x y
    exact ⟨g, g.property, hxy⟩
  have hTtransitive : PermutationSubgroupTransitive T := by
    intro x y
    obtain ⟨g, hg, hxy⟩ := htopTransitive
      (pointEquiv.symm x) (pointEquiv.symm y)
    refine ⟨pointEquiv.permCongr g, ?_, ?_⟩
    · change pointEquiv.permCongr g ∈
        block.Top.map pointEquiv.permCongrHom.toMonoidHom
      exact ⟨g, hg, rfl⟩
    · change pointEquiv (g (pointEquiv.symm x)) = y
      rw [hxy, pointEquiv.apply_symm_apply]
  have hTnonbinary : ¬ IsPGroup 2 T := by
    intro hT
    exact degreeFourZeroCoreTop_not_isPGroup_two block P hr hD
      (hT.of_equiv
        (pointEquiv.permCongrHom.subgroupMap block.Top).symm)
  let hselected := published T hTtransitive hTnonbinary
  let i : Fin 24 := Classical.choose hselected
  let hconjugator := Classical.choose_spec hselected
  let conjugator : Equiv.Perm (Fin 8) := Classical.choose hconjugator
  have hconjugated := Classical.choose_spec hconjugator
  exact ⟨i, {
    literalAction := (models i).literalAction
    actionModelEquiv := (models i).actionModelEquiv
    pointEquiv := pointEquiv
    conjugator := conjugator
    conjugated := hconjugated }⟩

/-- The exact remaining frame-matching obligation after the top has been
identified.  The representation and its sparse registries may be generated;
the only handwritten mathematical content here is the injective equivariant
map from the literal full frame. -/
structure DegreeFourZeroCoreEightLiteralFrameMatch
    (ModelGroup ModelModule : Type)
    [Group ModelGroup] [Finite ModelGroup]
    [AddCommGroup ModelModule]
    [Module (ZMod P.p) ModelModule]
    [FiniteDimensional (ZMod P.p) ModelModule]
    [Finite ModelModule]
    (representation : Representation
      (ZMod P.p) ModelGroup ModelModule)
    (groupEquiv : DegreeFourComplementQuotient block P ≃* ModelGroup) : Type where
  fullFrameEmbedding :
    (fullTranslationFrameRepresentation block P).IntertwiningMap
      (representation.comp groupEquiv.toMonoidHom)
  fullFrameEmbedding_injective : Function.Injective fullFrameEmbedding

namespace DegreeFourZeroCoreEightLiteralFrameMatch

/-- Attach the generated sparse top and module registries after the two
literal matching obligations have been discharged.  This constructor makes
the proof boundary explicit: the finite row supplies every argument after
`frameMatch`; no catalogue fact is used by the numerical consumer. -/
noncomputable def toSparseEmbeddedRow
    {ModelGroup ModelModule : Type}
    [Group ModelGroup] [Finite ModelGroup]
    [AddCommGroup ModelModule]
    [Module (ZMod P.p) ModelModule]
    [FiniteDimensional (ZMod P.p) ModelModule]
    [Finite ModelModule]
    (representation : Representation
      (ZMod P.p) ModelGroup ModelModule)
    (groupEquiv : DegreeFourComplementQuotient block P ≃* ModelGroup)
    (frameMatch : DegreeFourZeroCoreEightLiteralFrameMatch
      block P ModelGroup ModelModule representation groupEquiv)
    {classCount : ℕ}
    (representative : Fin classCount → ModelGroup)
    (conjugacyCover : FiniteConjugacyCardinalCover representative)
    {TopIndex AmbientIndex GeneratorIndex : Type}
    [Finite TopIndex]
    (ambient : AmbientIndex → ModelGroup)
    (stateGenerators : TopIndex → GeneratorIndex → ModelGroup)
    (top : FiniteTopRelativeBinaryRankWordRegistry
      (rank := 2) conjugacyCover ambient stateGenerators)
    (moduleRegistry : FiniteFrameModuleCyclicOrbitDisplacementRegistry
      representation 2) :
    DegreeFourZeroCoreEightSparseEmbeddedRow block P where
  ModelGroup := ModelGroup
  ModelModule := ModelModule
  representation := representation
  groupEquiv := groupEquiv
  fullFrameEmbedding := frameMatch.fullFrameEmbedding
  fullFrameEmbedding_injective := frameMatch.fullFrameEmbedding_injective
  classCount := classCount
  representative := representative
  conjugacyCover := conjugacyCover
  TopIndex := TopIndex
  AmbientIndex := AmbientIndex
  GeneratorIndex := GeneratorIndex
  ambient := ambient
  stateGenerators := stateGenerators
  top := top
  moduleRegistry := moduleRegistry

end DegreeFourZeroCoreEightLiteralFrameMatch

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
