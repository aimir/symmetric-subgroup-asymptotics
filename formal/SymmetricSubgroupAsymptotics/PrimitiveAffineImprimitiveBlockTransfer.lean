import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient
import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleSource
import SymmetricSubgroupAsymptotics.RefinedElementaryLayerEnvelope
import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceRankTailBridge
import Mathlib.Algebra.Module.ZMod

/-!
# The actual affine layer in an imprimitive block system

Let an original transitive action have an actual minimal block whose exact
component is primitive affine.  This file performs the structural transfer
on that block system itself.  It does not turn the component into a new
`PreE7NonPairActionClass`.

The point stabilizer of the affine component acts faithfully on the
nonidentity translations.  Apply this action in every coordinate of the
standard actual wreath embedding.  Its kernel is the literal intersection
of the original group with the product of the local translation groups.
The coordinate maps identify this kernel with an actual submodule of the
product of the local translation modules.  The quotient embeds faithfully
in the wreath product of the affine complements with the actual block top,
on exactly `(r - 1) * s` points.

This construction is valid at local degrees `2`, `3`, and `4`, and when the
whole affine component is a `2`-group.  No lower bound on the local degree
and no non-`2` hypothesis on the component occurs in the construction.
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
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

variable [Nontrivial block.Fibre]

abbrev Ambient := preE7NonPairAction w U

def origin : block.Fibre := ⟨basePoint, block.map_base⟩

abbrev primitive : MulAction.IsPreprimitive block.Component block.Fibre :=
  block.component_preprimitive

abbrev chart : P.ElementaryChart (primitive block) :=
  P.elementaryChart (primitive block)

abbrev localDegree : ℕ := Nat.card block.Fibre - 1

/-- The nonidentity translations, relabelled by a finite ordinal only at the
local permutation-action boundary. -/
def translationEquiv :
    P.NonidentityTranslation ≃ Fin (localDegree block) := by
  apply Equiv.trans (Finite.equivFin P.NonidentityTranslation)
  apply finCongr
  rw [P.nonidentity_card, P.card_eq (origin block)]

/-- The literal affine complement acting on the nonidentity translations. -/
def complementAction :
    P.complement (origin block) →* Equiv.Perm (Fin (localDegree block)) :=
  (translationEquiv block P).permCongrHom.toMonoidHom.comp
    (P.nonidentityAction (origin block))

theorem complementAction_injective :
    Function.Injective (complementAction block P) :=
  (translationEquiv block P).permCongrHom.injective.comp
    (P.nonidentityAction_injective (origin block))

abbrev LocalQuotient : Type := (complementAction block P).range

/-- The local compression map is the actual affine projection followed by
the faithful nonidentity-translation action. -/
def localMap : block.Component →* LocalQuotient block P :=
  (complementAction block P).rangeRestrict.comp
    (P.complementProjection (origin block))

theorem localMap_surjective : Function.Surjective (localMap block P) := by
  intro q
  obtain ⟨h, hh⟩ := q.2
  obtain ⟨g, hg⟩ := P.complementProjection_surjective (origin block) h
  refine ⟨g, Subtype.ext ?_⟩
  simpa [localMap, hh] using congrArg (complementAction block P) hg

/-- The local compression kernel is exactly the regular translation group.
This is the point at which faithfulness on nonidentity translations prevents
any accidental enlargement, including in characteristic two. -/
theorem localMap_ker :
    (localMap block P).ker = P.V := by
  rw [show P.V = (P.complementProjection (origin block)).ker from
    (P.complementProjection_ker (origin block)).symm]
  apply le_antisymm
  · intro g hg
    have hact : complementAction block P
        (P.complementProjection (origin block) g) = 1 := by
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
    have hc : P.complementProjection (origin block) g = 1 :=
      complementAction_injective block P (by simpa using hact)
    exact MonoidHom.mem_ker.mpr hc
  · intro g hg
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    change complementAction block P
        (P.complementProjection (origin block) g) = 1
    rw [MonoidHom.mem_ker.mp hg, map_one]

/-- Exact identification of the kernel of the compressed local map with the
chosen affine translation vector space. -/
def localKernelEquiv :
    Multiplicative (chart block P).V ≃* (localMap block P).ker :=
  (P.bottomKernelEquiv (primitive block) (chart block P) (origin block)).trans
    (MulEquiv.subgroupCongr
      ((P.complementProjection_ker (origin block)).trans
        (localMap_ker block P).symm))

/-- The standard actual wreath embedding attached to the original block
map. -/
def ambientEmbedding : preE7NonPairAction w U →*
    PermutationalWreathProduct block.Component block.Top block.Points :=
  ActualBlockWreathEmbedding.embedding block.map block.map_equivariant
    block.base

theorem ambientEmbedding_injective :
    Function.Injective (ambientEmbedding block) :=
  ActualBlockWreathEmbedding.embedding_injective block.map
    block.map_equivariant block.base

/-- The actual global translation intersection. -/
abbrev E : Subgroup (preE7NonPairAction w U) :=
  PermutationalWreathProduct.Compression.kernel
    (ambientEmbedding block) (localMap block P)

/-- One block coordinate of the actual translation intersection, expressed
in the fixed local translation vector space. -/
def coordinate (i : block.Points) :
    E block P →* Multiplicative (chart block P).V :=
  (localKernelEquiv block P).symm.toMonoidHom.comp
    (PermutationalWreathProduct.Compression.kernelCoordinate
      (ambientEmbedding block) (localMap block P) i)

/-- All actual block coordinates together.  Correlated and diagonal
translation kernels remain correlated in the range of this map. -/
def coordinates : E block P →*
    Multiplicative (block.Points → (chart block P).V) where
  toFun e := Multiplicative.ofAdd (fun i => (coordinate block P i e).toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    change (coordinate block P i 1).toAdd = 0
    simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext i
    change (coordinate block P i (a * b)).toAdd =
      (coordinate block P i a).toAdd + (coordinate block P i b).toAdd
    simp

theorem coordinates_injective : Function.Injective (coordinates block P) := by
  intro a b hab
  apply PermutationalWreathProduct.Compression.kernelCoordinate_joint_injective
    (ambientEmbedding block) (localMap block P)
      (ambientEmbedding_injective block)
  funext i
  apply (localKernelEquiv block P).symm.injective
  exact congrArg (fun z => Multiplicative.ofAdd (z.toAdd i)) hab

/-- Additive form of the joint coordinate map. -/
def coordinatesAdd : Additive (E block P) →+
    (block.Points → (chart block P).V) :=
  MonoidHom.toAdditiveLeft (coordinates block P)

theorem coordinatesAdd_injective :
    Function.Injective (coordinatesAdd block P) := by
  intro a b hab
  apply Additive.toMul.injective
  apply coordinates_injective block P
  exact congrArg Multiplicative.ofAdd hab

/-- The literal correlated translation submodule inside the product of the
local affine translation modules. -/
abbrev TranslationSubmodule :
    Submodule (ZMod P.p) (block.Points → (chart block P).V) :=
  AddSubgroup.toZModSubmodule P.p (coordinatesAdd block P).range

/-- The ambient translation intersection is exactly its literal coordinate
submodule; this is an equivalence onto the range, not an enlargement to the
full product. -/
def translationAddEquiv :
    Additive (E block P) ≃+ TranslationSubmodule block P :=
  AddEquiv.ofBijective (coordinatesAdd block P).rangeRestrict (by
    constructor
    ·
      intro a b hab
      apply coordinatesAdd_injective block P
      exact congrArg Subtype.val hab
    · exact (coordinatesAdd block P).rangeRestrict_surjective)

def translationMulEquiv :
    E block P ≃* Multiplicative (TranslationSubmodule block P) :=
  (translationAddEquiv block P).toMultiplicative

/-- Elementary chart for the actual ambient translation intersection.  The
name of the generic structure contains `MinimalNormal`, but its fields and
all downstream quotient constructions require only the exact elementary
coordinates supplied here. -/
def elementaryChart : ElementaryMinimalNormalChart (E block P) := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  exact
    { p := P.p
      p_prime := P.p_prime
      primeFact := (chart block P).primeFact
      V := TranslationSubmodule block P
      addCommGroup := inferInstance
      module := inferInstance
      finiteDimensional := FiniteDimensional.of_injective
        (TranslationSubmodule block P).subtype
        (TranslationSubmodule block P).subtype_injective
      equiv := translationMulEquiv block P }

/-- The quotient embedding retaining the literal affine complement and the
actual block top. -/
def quotientEmbedding :
    (preE7NonPairAction w U ⧸ E block P) →*
      PermutationalWreathProduct (LocalQuotient block P)
        block.Top block.Points :=
  PermutationalWreathProduct.Compression.quotientEmbedding
    (ambientEmbedding block) (localMap block P)

theorem quotientEmbedding_injective :
    Function.Injective (quotientEmbedding block P) :=
  PermutationalWreathProduct.Compression.quotientEmbedding_injective
    (ambientEmbedding block) (localMap block P)

theorem localDegree_pos : 0 < localDegree block := by
  have hr := block.degrees_ge_two.1
  dsimp only [localDegree]
  omega

def quotientDegree : ℕ :=
  localDegree block * Fintype.card block.Points

/-- The faithful quotient action on complement coordinates across the
actual block system. -/
def quotientAction :
    (preE7NonPairAction w U ⧸ E block P) →*
      Equiv.Perm (Fin (quotientDegree block)) := by
  letI : Nonempty (Fin (localDegree block)) :=
    Fin.pos_iff_nonempty.mp (localDegree_pos block)
  exact
    (PermutationalWreathProduct.toFintypePerm
      (u := localDegree block) (LocalQuotient block P)
        block.Top block.Points).comp (quotientEmbedding block P)

theorem quotientAction_injective :
    Function.Injective (quotientAction block P) := by
  letI : Nonempty (Fin (localDegree block)) :=
    Fin.pos_iff_nonempty.mp (localDegree_pos block)
  exact
    (PermutationalWreathProduct.toFintypePerm_injective
      (u := localDegree block) (LocalQuotient block P)
        block.Top block.Points).comp
      (quotientEmbedding_injective block P)

/-- Exact quotient degree: one deletes one translation point in every
actual block. -/
theorem quotientDegree_eq :
    quotientDegree block =
      (Nat.card block.Fibre - 1) * Nat.card block.Points := by
  simp [quotientDegree, localDegree]

/-- The original width is the local affine degree times the actual number of
blocks.  This is the literal fibre formula for the selected block map. -/
theorem width_eq :
    w = Nat.card block.Fibre * Nat.card block.Points := by
  have h := block.degree_product
  simpa using h.symm

/-- The complement action deletes exactly one point in every block.  Thus
the degree saved by the quotient comparator is the number of blocks, even in
characteristic two. -/
theorem quotientDegree_add_blockCount :
    quotientDegree block + Nat.card block.Points = w := by
  have hr := block.degrees_ge_two.1
  calc
    quotientDegree block + Nat.card block.Points =
        (Nat.card block.Fibre - 1) * Nat.card block.Points +
          Nat.card block.Points := by rw [quotientDegree_eq block]
    _ = ((Nat.card block.Fibre - 1) + 1) * Nat.card block.Points := by
      rw [add_mul, one_mul]
    _ = Nat.card block.Fibre * Nat.card block.Points := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ Nat.card block.Fibre)]
    _ = w := (width_eq block).symm

/-- Dimension is always a valid uniform Schur-capacity bound for every
literal descended section of the actual translation intersection.  Later
numerical refinements may replace it by the smaller induced-module capacity,
but no normal axis or extension datum is lost at this structural boundary. -/
def dimensionCapacity :
    ElementaryLayerSectionCapacityBound (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart where
  capacity := Module.finrank (ZMod (elementaryChart block P).p)
    (elementaryChart block P).V
  capacity_nonneg := by positivity
  section_capacity := by
    intro N
    letI : Finite (chart block P).V := Finite.of_injective
      (fun v : (chart block P).V =>
        (chart block P).equiv.symm (Multiplicative.ofAdd v))
      (chart block P).equiv.symm.injective
    letI : Finite (TranslationSubmodule block P) :=
      Finite.of_injective (TranslationSubmodule block P).subtype
        (TranslationSubmodule block P).subtype_injective
    letI : Finite (elementaryChart block P).V := by
      change Finite (TranslationSubmodule block P)
      infer_instance
    letI : Finite (elementaryChart block P).quotientRepresentation :=
      inferInstanceAs (Finite (elementaryChart block P).V)
    exact elementaryLayer_section_capacity_le
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart N

/-- The complete literal normal-axis weight of the original action transfers
through the actual affine translation intersection to the faithful quotient
action.  The same complementary permutation source `J` occurs on both sides;
restricted extensions, transgressions and `H¹` fibres are already included
in the one-layer envelope. -/
theorem completeQuotientWeight_le_translationLayer
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := preE7NonPairAction w U) J ≤
      elementaryLayerEnvelopeConstant (elementaryChart block P).p
          (QuotientGroup.mk' (E block P))
          (elementaryChart block P).quotientRepresentation
          (elementaryChart block P).originalKernelChart *
        ((elementaryChart block P).p : ℝ) ^
          ((dimensionCapacity block P).capacity *
            ((b : ℝ) / (elementaryChart block P).p)) *
        completeQuotientWeight
          (R := preE7NonPairAction w U ⧸ E block P) J := by
  letI : Finite (chart block P).V := Finite.of_injective
    (fun v : (chart block P).V =>
      (chart block P).equiv.symm (Multiplicative.ofAdd v))
    (chart block P).equiv.symm.injective
  letI : Finite (TranslationSubmodule block P) :=
    Finite.of_injective (TranslationSubmodule block P).subtype
      (TranslationSubmodule block P).subtype_injective
  letI : Finite (elementaryChart block P).V := by
    change Finite (TranslationSubmodule block P)
    infer_instance
  letI : Finite (elementaryChart block P).quotientRepresentation :=
    inferInstanceAs (Finite (elementaryChart block P).V)
  exact (dimensionCapacity block P).completeQuotientWeight_le
    (elementaryChart block P).p
    (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    (elementaryChart block P).quotientRepresentation
    (elementaryChart block P).originalKernelChart J

end PrimitiveAffineImprimitiveBlockTransfer

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
