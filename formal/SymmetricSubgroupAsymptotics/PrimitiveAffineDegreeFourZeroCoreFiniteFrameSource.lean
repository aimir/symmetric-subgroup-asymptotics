import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFiveCharacterIntervalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreSource
import SymmetricSubgroupAsymptotics.BinaryInvariantRegistry
import SymmetricSubgroupAsymptotics.BinaryKernelNormalRegistry
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead

/-!
# The finite-frame boundary for the degree-four zero core

The capacity argument leaves four, eight, and sixteen literal blocks.  Four
blocks have physical width sixteen and belong to the complete nonbinary
degree-sixteen owner.  The other two rows use the finite-frame bounds from
`computations/frames`: five faithful character positions at eight blocks and
ten at sixteen blocks.

This file deliberately does not turn the finite computation into a
literature hypothesis.  The finite rows concern only the literal top
`T = U/E` and its actual binary frame module.  They do not enumerate the
arbitrary extensions `U`, so they cannot directly construct a menu over all
normal subgroups of `U`.  `DegreeFourZeroCoreFiniteFrameBounds` records the
two semantic outputs which the literal rows can prove: a relative binary
head bound on every normal subgroup of `T`, and a coinvariant-head bound on
every invariant submodule of the actual translation representation.

`DegreeFourZeroCoreFixedFrameNoncentralSocleBridge` is the exact remaining
structural theorem: the fixed-frame argument adds those two bounds and the
noncentral-socle argument turns the resulting sectional-rank bound into a
whole-socle generator bound on every quotient of the original `U`.  The
source constructors require that theorem explicitly.  No field of the
finite certificate quantifies over arbitrary normal subgroups of `U`.

The finite checker still has to export the following literal bindings.

* At eight blocks: the top generators, point-stabilizer kernel, local
  `C3`/`S3` images, coset representatives, induced generators, binary basis,
  sixteen-dimensional generator matrices, and the complete list of
  invariant-submodule bases.
* At sixteen blocks: the top generators, stabilizer kernel, actual odd
  subgroup, actual normalizer element, and the recomputed relative binary
  rank and fixed-space dimension.

Those are data, not new assumptions.  An importer must check its row against
`degreeFourZeroCoreTopAction block P` and the quotient conjugation action in
`(elementaryChart block P).quotientRepresentation`; the generic bridge, not
the exporter, handles arbitrary original extensions and their quotients.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The unchanged normal-axis type used by the finite-frame checker. -/
abbrev DegreeFourZeroCoreFiniteFrameNormalAxis (G : Type) [Group G] :=
  {N : Subgroup G // N.Normal}

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The structural endpoint obtained after applying the generic bridge to
the imported finite-frame bounds.  A finite-row importer does not construct
this object directly: the socle bound quantifies over the original normal
axes of arbitrary `U`, beyond the top and module data enumerated by the
finite computation. -/
structure DegreeFourZeroCoreFiniteFrameVerification (slots : ℕ) : Prop where
  localDegree_eq_four : Nat.card block.Fibre = 4
  ternaryCore_eq_bot : degreeFourTernaryCore block P = ⊥
  literalTopAction_injective :
    Function.Injective (degreeFourZeroCoreTopAction block P)
  retainedSocleGenerators :
    ∀ N : DegreeFourZeroCoreFiniteFrameNormalAxis
        (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1) slots

/-- The finite top invariant appearing in the fixed-frame lemma.  This is
the dual form of the maximum rank of `L/[L,T]L^2`, with `L` running over
literal normal subgroups of the actual faithful top `T = U/E`. -/
def DegreeFourZeroCoreTopRelativeBinaryRankBound (rank : ℕ) : Prop :=
  ∀ L : DegreeFourZeroCoreFiniteFrameNormalAxis
      (DegreeFourComplementQuotient block P),
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 L.1) ≤ rank

/-- The finite module invariant appearing in the fixed-frame lemma.  It is
stated on the actual quotient conjugation representation of the correlated
translation intersection.  A checker for the full induced frame proves this
by embedding the correlated module in that frame and applying the complete
invariant-submodule registry. -/
def DegreeFourZeroCoreTranslationModuleHeadBound (rank : ℕ) : Prop :=
  ∀ B : Subrepresentation
      (elementaryChart block P).quotientRepresentation.ρ,
    Module.finrank (ZMod (elementaryChart block P).p)
      B.toRepresentation.Coinvariants ≤ rank

/-- Checkable normal-axis registry for the relative binary rank of one
literal finite top.  Completeness follows from point-adjoining closure in
`BinaryKernelNormalRegistry`, rather than from a row-count assertion. -/
structure FiniteTopRelativeBinaryRankRegistry
    (G : Type) [Group G] [Finite G] (rank : ℕ) : Type 1 where
  Index : Type
  [indexFinite : Finite Index]
  state : Index → Subgroup G
  normal : ∀ i, (state i).Normal
  axes : BinaryKernelNormalRegistry (⊤ : Subgroup G) state
  head_le : ∀ i,
    letI : (state i).Normal := normal i
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (state i)) ≤ rank

attribute [instance] FiniteTopRelativeBinaryRankRegistry.indexFinite

namespace FiniteTopRelativeBinaryRankRegistry

variable {G : Type} [Group G] [Finite G] {rank : ℕ}

/-- The local point-adjoining checks turn the recorded row bounds into the
relative binary bound on every literal normal subgroup of the top. -/
theorem bound (C : FiniteTopRelativeBinaryRankRegistry G rank)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ rank := by
  obtain ⟨i, hi⟩ := C.axes.complete N le_top
  subst N
  letI : (C.state i).Normal := C.normal i
  exact C.head_le i

end FiniteTopRelativeBinaryRankRegistry

/-- Checkable invariant-submodule registry for one literal binary frame.
At eight blocks this is the Lean boundary matching the 812 module lattices
in `frames8.json`: the states contain the literal bases and `axes` checks
closure under adjoining every cyclic orbit module. -/
structure FiniteFrameModuleHeadRegistry
    {k G V : Type} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (rank : ℕ) : Type 1 where
  Index : Type
  [indexFinite : Finite Index]
  state : Index → Subrepresentation ρ
  axes : BinaryInvariantRegistry ρ state
  head_le : ∀ i,
    Module.finrank k (state i).toRepresentation.Coinvariants ≤ rank

attribute [instance] FiniteFrameModuleHeadRegistry.indexFinite

namespace FiniteFrameModuleHeadRegistry

variable {k G V : Type} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {rank : ℕ}

/-- The cyclic-orbit closure checks cover every invariant submodule of the
literal frame, so the per-row head calculation gives the uniform bound. -/
theorem bound [Finite V] (C : FiniteFrameModuleHeadRegistry ρ rank)
    (B : Subrepresentation ρ) :
    Module.finrank k B.toRepresentation.Coinvariants ≤ rank := by
  obtain ⟨i, hi⟩ := C.axes.complete B
  subst B
  exact C.head_le i

end FiniteFrameModuleHeadRegistry

/-- Literal odd-subgroup/normalizer witness used by the sixteen-block
rows.  `fixed` is the subspace recomputed by the finite checker; its
membership equation ties the reported dimension to the actual subgroup
`A`, actual normalizer element `g`, and actual generator matrices. -/
structure FiniteFrameOddNormalizerWitness
    {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) : Type 1 where
  A : Subgroup G
  odd_order : ¬ 2 ∣ Nat.card A
  g : G
  g_normalizes : g ∈ Subgroup.normalizer (A : Set G)
  g_order_two_power : ∃ a : ℕ, orderOf g = 2 ^ a
  fixed : Submodule (ZMod 2) V
  mem_fixed_iff : ∀ v : V, v ∈ fixed ↔
    (∀ a : A, ρ a.1 v = v) ∧ ρ g v = v
  dimension : ℕ
  dimension_eq : Module.finrank (ZMod 2) fixed = dimension

/-- The literal finite-row shape for the eight-block calculation: a
complete normal registry for the top and a complete invariant-submodule
registry for its induced binary frame. -/
structure FiniteFrameRegistryRow
    {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (slots : ℕ) : Type 1 where
  topSlots : ℕ
  moduleSlots : ℕ
  slot_sum_le : topSlots + moduleSlots ≤ slots
  top : FiniteTopRelativeBinaryRankRegistry G topSlots
  module : FiniteFrameModuleHeadRegistry ρ moduleSlots

/-- The literal finite-row shape for the sixteen-block calculation.  It
retains the top normal registry and the actual odd subgroup and normalizer
element.  The generic odd-invariants/chain-ring theorem, rather than this
data object, must turn `fixed.dimension` into a uniform module-head bound. -/
structure FiniteFrameOddNormalizerRow
    {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (slots : ℕ) : Type 1 where
  topSlots : ℕ
  top : FiniteTopRelativeBinaryRankRegistry G topSlots
  fixedWitness : FiniteFrameOddNormalizerWitness ρ
  slot_sum_le : topSlots + fixedWitness.dimension ≤ slots

/-- A finite, locally checkable registry of socle-generating tuples on all
normal axes of one literal finite group.  Completeness is not a field: it is
proved by `BinaryKernelNormalRegistry.complete` from the checked closure
under adjoining the normal closure of every original group element.

This is a generic utility for a genuinely enumerated ambient group.  It is
not the finite-frame certificate below: the frame computations deliberately
do not enumerate the arbitrary degree-32 or degree-64 extension `U`, so
their rows cannot construct this registry. -/
structure FiniteSocleGeneratorRegistry
    (G : Type) [Group G] [Finite G] (slots : ℕ) : Type 1 where
  Index : Type
  [indexFinite : Finite Index]
  state : Index → Subgroup G
  normal : ∀ i, (state i).Normal
  axes : BinaryKernelNormalRegistry (⊤ : Subgroup G) state
  generators : ∀ i,
    letI : (state i).Normal := normal i
    Fin slots → G ⧸ state i
  generated : ∀ i,
    letI : (state i).Normal := normal i
    Subgroup.normalClosure (Set.range (generators i)) =
      finiteGroupSocle (G ⧸ state i)

attribute [instance] FiniteSocleGeneratorRegistry.indexFinite

namespace FiniteSocleGeneratorRegistry

variable {G : Type} [Group G] [Finite G] {slots : ℕ}

/-- Local point-adjoining checks make the exported normal-axis menu
complete, and the tuple stored at the matching row gives the required
socle bound. -/
noncomputable def bound (C : FiniteSocleGeneratorRegistry G slots)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) slots := by
  obtain ⟨i, hi⟩ := C.axes.complete N le_top
  subst N
  letI : (C.state i).Normal := C.normal i
  exact ⟨C.generators i, C.generated i⟩

end FiniteSocleGeneratorRegistry

/-- The semantic output of one literal finite-frame row.  `topSlots` and
`moduleSlots` remain separate so the imported row retains its recomputed top
rank and module-head/fixed-space entries.  At eight blocks they are at most
two and two; at sixteen blocks their row-wise sum is at most ten. -/
structure DegreeFourZeroCoreFiniteFrameBounds (slots : ℕ) : Type 1 where
  topSlots : ℕ
  moduleSlots : ℕ
  slot_sum_le : topSlots + moduleSlots ≤ slots
  topRelativeBinaryRank :
    DegreeFourZeroCoreTopRelativeBinaryRankBound block P topSlots
  translationModuleHead :
    DegreeFourZeroCoreTranslationModuleHeadBound block P moduleSlots

namespace DegreeFourZeroCoreFiniteFrameBounds

/-- Direct registry importer when the checked module is already the actual
correlated translation representation.  The eight-block full-frame
importer has one additional, routine step: restrict its complete ambient
registry bound along the checked embedding of the actual correlated module. -/
noncomputable def ofRegistries {slots topSlots moduleSlots : ℕ}
    [Finite (elementaryChart block P).V]
    (slot_sum_le : topSlots + moduleSlots ≤ slots)
    (top : FiniteTopRelativeBinaryRankRegistry
      (DegreeFourComplementQuotient block P) topSlots)
    (module : FiniteFrameModuleHeadRegistry
      (elementaryChart block P).quotientRepresentation.ρ moduleSlots) :
    DegreeFourZeroCoreFiniteFrameBounds block P slots where
  topSlots := topSlots
  moduleSlots := moduleSlots
  slot_sum_le := slot_sum_le
  topRelativeBinaryRank := by
    intro L
    letI : L.1.Normal := L.2
    exact top.bound L.1
  translationModuleHead := by
    intro B
    exact FiniteFrameModuleHeadRegistry.bound
      (V := (elementaryChart block P).V)
      (ρ := (elementaryChart block P).quotientRepresentation.ρ)
      module B

end DegreeFourZeroCoreFiniteFrameBounds

/-- The exact structural theorem still required between the finite rows and
the whole-socle character interval.  Its fixed-frame half uses the two
bounds above to control the trivial binary socle type in every quotient of
the arbitrary original extension.  Its noncentral half supplies the other
simple types.  This statement contains no finite classification premise. -/
def DegreeFourZeroCoreFixedFrameNoncentralSocleBridge (slots : ℕ) : Prop :=
  Nat.card block.Fibre = 4 →
    degreeFourTernaryCore block P = ⊥ →
    ∀ _C : DegreeFourZeroCoreFiniteFrameBounds block P slots,
    (Nat.card block.Points = 8 ∨ Nat.card block.Points = 16) →
    ∀ N : DegreeFourZeroCoreFiniteFrameNormalAxis
        (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1) slots

namespace DegreeFourZeroCoreFiniteFrameBounds

/-- Apply the generic fixed-frame/noncentral-socle theorem to a checked
literal row.  Faithfulness of the top action follows internally from the
stored degree and zero-core equations. -/
noncomputable def toVerification {slots : ℕ}
    (bridge : DegreeFourZeroCoreFixedFrameNoncentralSocleBridge
      block P slots)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8 ∨ Nat.card block.Points = 16)
    (C : DegreeFourZeroCoreFiniteFrameBounds block P slots) :
    DegreeFourZeroCoreFiniteFrameVerification block P slots where
  localDegree_eq_four := hr
  ternaryCore_eq_bot := hD
  literalTopAction_injective :=
    degreeFourZeroCoreTopAction_injective block P hr hD
  retainedSocleGenerators := bridge hr hD C hs

end DegreeFourZeroCoreFiniteFrameBounds

/-- Package a checked finite-frame row as a character interval without
changing the translation subgroup, quotient action, or normal-axis set. -/
noncomputable def degreeFourZeroCoreFiniteFrameInterval
    {slots : ℕ}
    (verified : DegreeFourZeroCoreFiniteFrameVerification block P slots) :
    SocleGeneratorCharacterIntervalData (preE7NonPairAction w U) where
  E := E block P
  quotientDegree := quotientDegree block
  quotientAction := quotientAction block P
  quotientAction_injective := quotientAction_injective block P
  slots := slots
  quotientSocleGenerators := verified.retainedSocleGenerators

private theorem logb_two_five_lt_seven_thirds_zeroCoreFrames :
    Real.logb 2 5 < (7 : ℝ) / 3 := by
  have hp : (5 : ℝ) ^ (3 : ℕ) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (5 : ℝ) ^ (3 : ℕ)) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by
    simpa only [mul_comm] using hlog)

theorem degreeFourZeroCore_fiveSlot_window :
    (5 : ℝ) * (Real.logb 2 5 / 3) ≤ preE7CharacterWindow 32 := by
  have hlog := logb_two_five_lt_seven_thirds_zeroCoreFrames
  norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree] at hlog ⊢
  linarith

theorem degreeFourZeroCore_tenSlot_window :
    (10 : ℝ) * (Real.logb 2 5 / 3) ≤ preE7CharacterWindow 64 := by
  have hlog := logb_two_five_lt_seven_thirds_zeroCoreFrames
  norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree] at hlog ⊢
  linarith

/-- The source attached to a checked eight-block finite frame.  The five
slots are the manuscript's finite-frame cover; no replacement four-slot
claim is made. -/
noncomputable def degreeFourZeroCoreEightBlockSource_of_verifiedFrames
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (bridge : DegreeFourZeroCoreFixedFrameNoncentralSocleBridge
      block P 5)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8)
    (certificate : DegreeFourZeroCoreFiniteFrameBounds block P 5) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let verified := DegreeFourZeroCoreFiniteFrameBounds.toVerification
    block P bridge hr hD (Or.inl hs) certificate
  let D := (degreeFourZeroCoreFiniteFrameInterval block P verified
    ).toCompleteCharacterIntervalData hZmud
  have hw : w = 32 := by
    calc
      w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
      _ = 4 * 8 := by rw [verified.localDegree_eq_four, hs]
      _ = 32 := by norm_num
  apply boundedCompleteCharacterSource D lit .acomp
  · change preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - (max 2 (quotientDegree block) : ℕ)) / 8
    have hq : quotientDegree block = 3 * Nat.card block.Points :=
      degreeFour_quotientDegree_eq_three_mul block
        verified.localDegree_eq_four
    have hlhs : preE7CharacterRho * (w : ℝ) =
        preE7CharacterRho * (32 : ℝ) := by norm_num [hw]
    have heven : evenWidth w = evenWidth 32 := congrArg evenWidth hw
    rw [hlhs, heven, hq, hs]
    convert degreeFour_comparator_margin_of_width 8 (by norm_num) using 1 <;>
      norm_num
  · change (5 : ℝ) * (Real.logb 2 5 / 3) ≤ preE7CharacterWindow w
    rw [hw]
    exact degreeFourZeroCore_fiveSlot_window
  · omega

/-- The source attached to a checked sixteen-block finite frame.  The ten
slots retain the literal odd-subgroup/normalizer fixed-space certificate. -/
noncomputable def degreeFourZeroCoreSixteenBlockSource_of_verifiedFrames
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (bridge : DegreeFourZeroCoreFixedFrameNoncentralSocleBridge
      block P 10)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 16)
    (certificate : DegreeFourZeroCoreFiniteFrameBounds block P 10) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let verified := DegreeFourZeroCoreFiniteFrameBounds.toVerification
    block P bridge hr hD (Or.inr hs) certificate
  let D := (degreeFourZeroCoreFiniteFrameInterval block P verified
    ).toCompleteCharacterIntervalData hZmud
  have hw : w = 64 := by
    calc
      w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
      _ = 4 * 16 := by rw [verified.localDegree_eq_four, hs]
      _ = 64 := by norm_num
  apply boundedCompleteCharacterSource D lit .acomp
  · change preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - (max 2 (quotientDegree block) : ℕ)) / 8
    have hq : quotientDegree block = 3 * Nat.card block.Points :=
      degreeFour_quotientDegree_eq_three_mul block
        verified.localDegree_eq_four
    have hlhs : preE7CharacterRho * (w : ℝ) =
        preE7CharacterRho * (64 : ℝ) := by norm_num [hw]
    have heven : evenWidth w = evenWidth 64 := congrArg evenWidth hw
    rw [hlhs, heven, hq, hs]
    convert degreeFour_comparator_margin_of_width 16 (by norm_num) using 1 <;>
      norm_num
  · change (10 : ℝ) * (Real.logb 2 5 / 3) ≤ preE7CharacterWindow w
    rw [hw]
    exact degreeFourZeroCore_tenSlot_window
  · omega

/-- Four degree-four affine blocks have physical width sixteen. -/
theorem degreeFourZeroCore_fourBlocks_width
    (hr : Nat.card block.Fibre = 4)
    (hs : Nat.card block.Points = 4) : w = 16 := by
  calc
    w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
    _ = 4 * 4 := by rw [hr, hs]
    _ = 16 := by norm_num

/-- The supplied degree-sixteen owner is applied to the same literal
`PreE7NonPairActionClass`; the equality substitution does not introduce a
relabelled action. -/
noncomputable def degreeFourZeroCoreFourBlockSource_of_degreeSixteenOwner
    (degreeSixteenOwner : ∀ V : PreE7NonPairActionClass 16,
      PreE7RankTailSourceOrYonedaTopData 16 V)
    (hr : Nat.card block.Fibre = 4)
    (hs : Nat.card block.Points = 4) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  have hw : w = 16 := degreeFourZeroCore_fourBlocks_width block hr hs
  subst w
  exact degreeSixteenOwner U

/-- One local split for the three nonempty finite residues.  The finite
checker supplies the two literal top/module bound objects, the generic
fixed-frame/noncentral-socle theorem converts them to original quotient
menus, and the separate degree-sixteen catalogue supplies the four-block
owner. -/
noncomputable def degreeFourZeroCoreFiniteResidueSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (degreeSixteenOwner : ∀ V : PreE7NonPairActionClass 16,
      PreE7RankTailSourceOrYonedaTopData 16 V)
    (bridge8 : DegreeFourZeroCoreFixedFrameNoncentralSocleBridge
      block P 5)
    (bridge16 : DegreeFourZeroCoreFixedFrameNoncentralSocleBridge
      block P 10)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (frames8 : Nat.card block.Points = 8 →
      DegreeFourZeroCoreFiniteFrameBounds block P 5)
    (frames16 : Nat.card block.Points = 16 →
      DegreeFourZeroCoreFiniteFrameBounds block P 10)
    (hs : Nat.card block.Points = 4 ∨
      Nat.card block.Points = 8 ∨ Nat.card block.Points = 16) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  classical
  by_cases hs4 : Nat.card block.Points = 4
  · exact degreeFourZeroCoreFourBlockSource_of_degreeSixteenOwner block P
      degreeSixteenOwner hr hs4
  by_cases hs8 : Nat.card block.Points = 8
  · exact degreeFourZeroCoreEightBlockSource_of_verifiedFrames block P
      hZmud lit bridge8 hr hD hs8 (frames8 hs8)
  have hs16 : Nat.card block.Points = 16 :=
    (hs.resolve_left hs4).resolve_left hs8
  exact degreeFourZeroCoreSixteenBlockSource_of_verifiedFrames block P
    hZmud lit bridge16 hr hD hs16 (frames16 hs16)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
