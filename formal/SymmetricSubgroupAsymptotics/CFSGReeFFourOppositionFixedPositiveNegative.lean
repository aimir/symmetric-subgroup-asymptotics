import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveFamilies
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeWord
import SymmetricSubgroupAsymptotics.CFSGConjugateComap

/-! Actual opposition of the positive and negative preimages in the
original exceptional-fixed group and the pinned fixedSubgroup. Preimage
transport uses an arbitrary homomorphism; no injectivity, quotient lift,
whole positive-group recognition, or derived-group claim is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionFixedPositiveNegative
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourRelativeOpposition CFSGReeFFourRelativeOppositionLattice
open CFSGReeFFourOriginalAutomorphism CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoCoordinateOppositeWord
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckOppositeIntersection
open CFSGNormTwoCoordinateHeight CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6GeckPositiveTwist
open CFSGConjugateComap
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem ambient_positive_image_le_negative (K : Type) [_root_.Field K] :
    (Positive K).map
      (MulAut.conj (wordUnit A hs hp E6Base E6Index K relativeOppositionWord)).toMonoidHom≤
        rootGroup A hs hp E6Base E6Index K true := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i,t⟩,rfl⟩
  exact negative_word_mem A hd hs hp ho K relativeOppositionWord i t
    (relative_opposition_simple_nonpositive i)

theorem ambient_positive_image_eq_negative (K : Type) [_root_.Field K] [Finite K] :
    (Positive K).map
      (MulAut.conj (wordUnit A hs hp E6Base E6Index K relativeOppositionWord)).toMonoidHom=
        rootGroup A hs hp E6Base E6Index K true := by
  have hi : Positive K⊓(Positive K).map
      (MulAut.conj (wordUnit A hs hp E6Base E6Index K relativeOppositionWord)).toMonoidHom=⊥ := by
    apply le_antisymm _ bot_le
    exact (inf_le_inf le_rfl (ambient_positive_image_le_negative K)).trans
      (le_of_eq (positive_inf_negative A hs hp E6Base E6Index coordinateHeight
        (simple_height A hd hs hp ho) K))
  exact word_positive_map_eq_negative_of_disjoint A hd hs hp ho K relativeOppositionWord hi

def fixedNegative (m : ℕ) : Subgroup (originalModelFixed m) :=
  (rootGroup A hs hp E6Base E6Index (Field m) true).comap (fixedRawHom m)

def oppositionFixed (m : ℕ) : originalModelFixed m :=
  ⟨relativeOpposition m,relativeOpposition_fixed m⟩

theorem fixedRawHom_oppositionFixed (m : ℕ) :
    fixedRawHom m (oppositionFixed m)=
      wordUnit A hs hp E6Base E6Index (Field m) relativeOppositionWord := by
  change CFSGFFourOriginalMiddleWords.rawHom (Field m) (relativeOpposition m)=_
  exact rawHom_relativeOpposition m

theorem fixed_positive_image_eq_fixed_negative (m : ℕ) :
    (fixedPositive m).map (MulAut.conj (oppositionFixed m)).toMonoidHom=fixedNegative m := by
  have hraw : (Positive (Field m)).map
      (MulAut.conj (fixedRawHom m (oppositionFixed m))).toMonoidHom=
        rootGroup A hs hp E6Base E6Index (Field m) true := by
    rw [fixedRawHom_oppositionFixed]
    exact ambient_positive_image_eq_negative (Field m)
  calc
    _=((Positive (Field m)).map
        (MulAut.conj (fixedRawHom m (oppositionFixed m))).toMonoidHom).comap (fixedRawHom m) :=
      (comap_conjugate (fixedRawHom m) (Positive (Field m)) (oppositionFixed m)).symm
    _=fixedNegative m := congrArg
      (fun S : Subgroup (Matrix CFSGFFourSerreMatrices.Index CFSGFFourSerreMatrices.Index
        (Field m))ˣ=>S.comap (fixedRawHom m)) hraw

def originalFixedNegative (m : ℕ) : Subgroup
    (fixedSubgroup CartanMatrix.F₄ (Field m) CFSG.Models.reverseNode (originalExponent m)) :=
  (fixedNegative m).comap (originalFixedEquiv m).toMonoidHom

def originalOppositionFixed (m : ℕ) :
    fixedSubgroup CartanMatrix.F₄ (Field m) CFSG.Models.reverseNode (originalExponent m) :=
  (originalFixedEquiv m).symm (oppositionFixed m)

theorem original_fixed_positive_image_eq_fixed_negative (m : ℕ) :
    (originalFixedPositive m).map (MulAut.conj (originalOppositionFixed m)).toMonoidHom=
      originalFixedNegative m := by
  have he : originalFixedEquiv m (originalOppositionFixed m)=oppositionFixed m :=
    (originalFixedEquiv m).apply_symm_apply (oppositionFixed m)
  have hgeom : (fixedPositive m).map
      (MulAut.conj ((originalFixedEquiv m).toMonoidHom (originalOppositionFixed m))).toMonoidHom=
        fixedNegative m := by
    change (fixedPositive m).map
      (MulAut.conj (originalFixedEquiv m (originalOppositionFixed m))).toMonoidHom=_
    rw [he]
    exact fixed_positive_image_eq_fixed_negative m
  calc
    _=((fixedPositive m).map
        (MulAut.conj ((originalFixedEquiv m).toMonoidHom
          (originalOppositionFixed m))).toMonoidHom).comap (originalFixedEquiv m).toMonoidHom :=
      (comap_conjugate (originalFixedEquiv m).toMonoidHom
        (fixedPositive m) (originalOppositionFixed m)).symm
    _=originalFixedNegative m :=
      congrArg (fun S : Subgroup (originalModelFixed m)=>
        S.comap (originalFixedEquiv m).toMonoidHom) hgeom

end SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionFixedPositiveNegative
