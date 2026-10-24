import SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleFunctionalSupport
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeBorelFactors
import SymmetricSubgroupAsymptotics.CFSGReeFFourMinimalParabolics
import SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleInversionBlocks
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeFunctionalFlag

/-! The actual positive group intersects each literal opposite relative
candidate in precisely its already-counted fixed inversion block. The
forward inclusion is the proved integral support-cone criterion; the
reverse inclusion is genuine conjugation by its contained Weyl element.
No additional root census, rank-one presentation or fixed-point lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeParabolicRootIntersection
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBruhatCover
open CFSGReeFFourBorelIntersection CFSGReeFFourOppositeBorelFactors
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourMinimalParabolics
open CFSGReeFFourSimpleFunctionalSupport CFSGReeFFourSimpleInversionBlocks
open CFSGReeFFourPairedDescentPrefixes CFSGReeFFourOriginalWeylWords
open CFSGReeFFourFixedWordClassification CFSGReeFFourPairedWordActions
open CFSGTwistedE6FixedWordClassification CFSGNormTwoGeckIntegralWord
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckNormalizerEnvelope CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckNonnegativeHeightFlag
open CFSGGradedMatrixSubgroups CFSGGradedMatrixTriangularUnits
open CFSGNormTwoCoordinateOppositeFunctionalFlag CFSGNormTwoGeckWeylWordDegree
open CFSGOpposedSubgroupPeeling
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

def simpleFlag (K : Type) [_root_.Field K] (middle : Bool) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  triangularUnits (weight A hs hp E6Base (simpleFunctional middle))

def negativeSimpleParabolic (m : ℕ) (middle : Bool) : Subgroup (originalModelFixed m) :=
  oppositeBorel m⊔Subgroup.closure {simpleWeyl m middle}

theorem fixedRawHom_simpleWeyl (m : ℕ) (middle : Bool) :
    fixedRawHom m (simpleWeyl m middle)=
      wordUnit A hs hp E6Base E6Index (Field m) (pairedWord middle) := by
  rw [fixedRawHom_apply]
  change CFSGFFourOriginalMiddleWords.rawHom (Field m)
    (modelWeylWord (Field m) (expandPaired [middle]))=_
  rw [rawHom_modelWeylWord_relative]
  simp only [expandPaired,List.append_nil,expand_pairedRelativeWord]

private theorem negative_le_simpleFlag (K : Type) [_root_.Field K] (middle : Bool) :
    Negative K≤simpleFlag K middle := by
  apply negative_le_functional_triangular A hd hs hp ho K (simpleFunctional middle)
  intro i
  change 0≤simpleFunctional middle (E6Index i : Roots A).val
  rw [simpleFunctional_simple]
  split_ifs <;> omega

private theorem diagonal_le_simpleFlag (K : Type) [_root_.Field K] (middle : Bool) :
    diagonalNormalizer K≤simpleFlag K middle := by
  intro d hdD
  have hdiag := diagonalNormalizer_isDiag K d hdD
  intro i j hij
  exact hdiag (by intro he;subst j;exact lt_irrefl _ hij)

private theorem simple_word_mem_flag (K : Type) [_root_.Field K] (middle : Bool) :
    wordUnit A hs hp E6Base E6Index K (pairedWord middle)∈simpleFlag K middle := by
  have hz : ∀i∈pairedWord middle,simpleFunctional middle (E6Index i : Roots A).val=0 := by
    intro i hi
    exact simpleFunctional_zero_word middle i hi
  have hpres := zero_degree_word_preserving A hs hp E6Base E6Index
    (simpleFunctional middle) K (pairedWord middle) hz
  have ht := preserving_le_triangular (weight A hs hp E6Base (simpleFunctional middle)) hpres
  simpa only [word_eq_canonicalWord] using ht

theorem negativeSimpleParabolic_le_flag (m : ℕ) (middle : Bool) :
    negativeSimpleParabolic m middle≤(simpleFlag (Field m) middle).comap (fixedRawHom m) := by
  apply sup_le
  · rw [oppositeBorel_eq_sup]
    apply sup_le
    · intro v hv
      exact negative_le_simpleFlag (Field m) middle hv
    · intro d hdD
      exact diagonal_le_simpleFlag (Field m) middle hdD
  · apply (Subgroup.closure_le _).mpr
    apply Set.singleton_subset_iff.mpr
    change fixedRawHom m (simpleWeyl m middle)∈simpleFlag (Field m) middle
    rw [fixedRawHom_simpleWeyl]
    exact simple_word_mem_flag (Field m) middle

theorem positive_inf_negativeSimpleParabolic_eq_inversion (m : ℕ) (middle : Bool) :
    fixedPositive m⊓negativeSimpleParabolic m middle=
      inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m middle) := by
  apply le_antisymm
  · intro x hx
    have hr := positive_inf_simple_flag_le_inversion (Field m) middle
      ⟨hx.1,negativeSimpleParabolic_le_flag m middle hx.2⟩
    refine ⟨hx.1,?_⟩
    change fixedRawHom m (simpleWeyl m middle*x*(simpleWeyl m middle)⁻¹)∈Negative (Field m)
    rw [map_mul,map_mul,map_inv,fixedRawHom_simpleWeyl]
    exact hr.2
  · intro x hx
    have hw : simpleWeyl m middle∈negativeSimpleParabolic m middle :=
      (show Subgroup.closure {simpleWeyl m middle}≤negativeSimpleParabolic m middle from le_sup_right)
        (Subgroup.subset_closure (Set.mem_singleton _))
    have hn : simpleWeyl m middle*x*(simpleWeyl m middle)⁻¹∈negativeSimpleParabolic m middle :=
      (show oppositeBorel m≤negativeSimpleParabolic m middle from le_sup_left)
        (negative_le_oppositeBorel m hx.2)
    have hh := (negativeSimpleParabolic m middle).mul_mem
      ((negativeSimpleParabolic m middle).mul_mem ((negativeSimpleParabolic m middle).inv_mem hw) hn) hw
    have he : (simpleWeyl m middle)⁻¹*(simpleWeyl m middle*x*(simpleWeyl m middle)⁻¹)*
        simpleWeyl m middle=x := by group
    exact ⟨hx.1,he ▸ hh⟩

theorem positive_inf_negativeSimpleParabolic_eq_block (m : ℕ) (middle : Bool) :
    fixedPositive m⊓negativeSimpleParabolic m middle=
      if middle then CFSGReeFFourMiddleFixedInversion.fixedMiddleInversion m
      else CFSGReeFFourOuterFixedInversion.fixedOuterInversion m := by
  rw [positive_inf_negativeSimpleParabolic_eq_inversion]
  exact simple_inversion_eq_block m middle

theorem positive_inf_negativeSimpleParabolic_card (m : ℕ) (middle : Bool) :
    Nat.card ↥((fixedPositive m⊓negativeSimpleParabolic m middle) : Subgroup (originalModelFixed m))=
      (2^(2*m+1))^(if middle then 2 else 1) := by
  rw [positive_inf_negativeSimpleParabolic_eq_inversion]
  exact simple_inversion_card m middle

end SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeParabolicRootIntersection
