import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedSubgroup
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterFixedRoot

/-! The actual original exceptional-fixed positive subgroup, defined as
the preimage of ambient E6 positivity. Its already-constructed outer and
middle parameter subgroups lie in it. No generation or Sylow statement
is made here, including at the Tits parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveFamilies
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourMiddleFixedSubgroup
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleWordInjective
open CFSGReeFFourOuterFixedRoot CFSGFFourOriginalMiddleWords
open CFSGTwistedE6GeckPositiveTwist CFSGNormTwoCoordinateLeadingHom
open CFSGExceptionalCartanPositiveDefinite CFSGSerreQuadraticMatrix
open CFSGFFourE6FixedGeneratedGroup CFSGTwistedE6GeckDiagramCovariance
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def fixedRawHom (m : ℕ) :=
  (rawHom (Field m)).comp (originalModelFixed m).subtype

theorem fixedRawHom_apply (m : ℕ) (g : originalModelFixed m) :
    fixedRawHom m g=rawHom (Field m) g.val := rfl

def fixedPositive (m : ℕ) : Subgroup (originalModelFixed m) :=
  (Positive (Field m)).comap (fixedRawHom m)

theorem middleFixedSubgroup_le_fixedPositive (m : ℕ) :
    middleFixedSubgroup m≤fixedPositive m := by
  rintro g ⟨a,b,c,d,hg⟩
  change rawHom (Field m) g.val∈Positive (Field m)
  rw [←hg,rawHom_middleWord]
  exact (matrixMiddleWord (Field m) a b c d).property

theorem fixedOuterHom_range_le_fixedPositive (m : ℕ) :
    (fixedOuterHom m).range≤fixedPositive m := by
  rintro g ⟨a,rfl⟩
  change rawHom (Field m) (outerWord m a.toAdd)∈Positive (Field m)
  simp only [outerWord,map_mul,rawHom_root,folded_root_eq_orbitParameter]
  change (canonicalRoot rawData (Field m) false 0 a.toAdd*
    canonicalRoot rawData (Field m) false 5 a.toAdd)*
      canonicalRoot rawData (Field m) false 1 (alpha m a.toAdd)∈Positive (Field m)
  exact (Positive (Field m)).mul_mem
    ((Positive (Field m)).mul_mem
      (positiveRoot A hd hs hp ho (Field m) 0 a.toAdd).property
      (positiveRoot A hd hs hp ho (Field m) 5 a.toAdd).property)
    (positiveRoot A hd hs hp ho (Field m) 1 (alpha m a.toAdd)).property

def originalFixedPositive (m : ℕ) : Subgroup
    (fixedSubgroup CartanMatrix.F₄ (Field m) CFSG.Models.reverseNode (originalExponent m)) :=
  (fixedPositive m).comap (originalFixedEquiv m).toMonoidHom

theorem originalMiddleFixedSubgroup_le_originalFixedPositive (m : ℕ) :
    originalMiddleFixedSubgroup m≤originalFixedPositive m := by
  intro g hg
  exact middleFixedSubgroup_le_fixedPositive m hg

theorem originalFixedOuterHom_range_le_originalFixedPositive (m : ℕ) :
    (originalFixedOuterHom m).range≤originalFixedPositive m := by
  rintro g ⟨a,rfl⟩
  change originalFixedEquiv m ((originalFixedEquiv m).symm (fixedOuterHom m a))∈fixedPositive m
  rw [(originalFixedEquiv m).apply_symm_apply]
  exact fixedOuterHom_range_le_fixedPositive m ⟨a,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveFamilies
