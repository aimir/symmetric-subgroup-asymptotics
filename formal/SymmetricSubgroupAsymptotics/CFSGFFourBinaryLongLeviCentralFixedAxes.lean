import SymmetricSubgroupAsymptotics.CFSGFFourBinaryCentralCoordinateWords
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroupCommute
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveRootUnits

/-! The remaining central axes fixed by the actual positive long Levi
parameter. Together with the nontrivial quadratic correction, these are
literal generator identities, before any binary linear-action claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviCentralFixedAxes
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGFFourE6HeisenbergLeviRoots CFSGFFourBinaryCentralCoordinateWords
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootSubgroupCommute
open CFSGFFourSerreMatrices CFSGFFourE6PositiveRootUnits CFSGSerreQuadraticMatrix
open CFSGExceptionalHeisenbergRootRelations
local instance fFourLongFixedAxesRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) :=
  Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private theorem first_pairing (i : Fin 3) (hi : i ≠ 2) :
    integerPairing A (configuration.x (pairPick i))
        (coordinateIndexEquiv A hd hs hp ho 3 : Roots A).val=0 ∧
    integerPairing A (configuration.x (partner (pairPick i)))
        (coordinateIndexEquiv A hd hs hp ho 3 : Roots A).val=0 := by
  fin_cases i <;> try exact False.elim (hi rfl)
  all_goals decide

private theorem second_pairing (i : Fin 3) :
    (integerPairing A (configuration.y (pairPick i))
        (coordinateIndexEquiv A hd hs hp ho 3 : Roots A).val=0 ∨
      integerPairing A (configuration.y (pairPick i))
        (coordinateIndexEquiv A hd hs hp ho 3 : Roots A).val=1) ∧
    (integerPairing A (configuration.y (partner (pairPick i)))
        (coordinateIndexEquiv A hd hs hp ho 3 : Roots A).val=0 ∨
      integerPairing A (configuration.y (partner (pairPick i)))
        (coordinateIndexEquiv A hd hs hp ho 3 : Roots A).val=1) := by
  fin_cases i <;> decide

private theorem long_commute (K : Type) [Field K] (k : Roots A)
    (hk : integerPairing A k.val (coordinateIndexEquiv A hd hs hp ho 3 : Roots A).val=0 ∨
      integerPairing A k.val (coordinateIndexEquiv A hd hs hp ho 3 : Roots A).val=1)
    (a t : K) :
    Commute (canonicalRoot realizationData K false 2 a)
      (selectedRootElement A hd hs hp ho K k t) := by
  rw [folded_positive_root]
  exact (rootSubgroup_pair_commute A hd hs hp ho K k
    (coordinateIndexEquiv A hd hs hp ho 3) hk _ _
    (selectedRootElement_mem A hd hs hp ho K k t)
    (canonicalRoot_mem_rootSubgroup A hd hs hp ho K 3 a)).symm

theorem long_positive_commutes_central_first (K : Type) [Field K] [CharP K 2]
    (i : Fin 3) (hi : i ≠ 2) (a t : K) :
    Commute (canonicalRoot realizationData K false 2 a)
      (centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single i t,0)))) := by
  rw [central_first_word]
  change Commute (canonicalRoot realizationData K false 2 a)
    (selectedRootElement A hd hs hp ho K (configuration.xRoot (pairPick i)).val t *
      selectedRootElement A hd hs hp ho K (configuration.xRoot (partner (pairPick i))).val t)
  have hfirst := long_commute K (configuration.xRoot (pairPick i)).val
    (Or.inl (first_pairing i hi).1) a t
  have hpartner := long_commute K (configuration.xRoot (partner (pairPick i))).val
    (Or.inl (first_pairing i hi).2) a t
  exact hfirst.mul_right hpartner

theorem long_positive_commutes_central_second (K : Type) [Field K] [CharP K 2]
    (i : Fin 3) (a t : K) :
    Commute (canonicalRoot realizationData K false 2 a)
      (centralMatrixHom K (Multiplicative.ofAdd (0,(0,Pi.single i t)))) := by
  rw [central_second_word]
  change Commute (canonicalRoot realizationData K false 2 a)
    (selectedRootElement A hd hs hp ho K (configuration.yRoot (pairPick i)).val
        (((pairSign A hd hs hp ho configuration (pairPick i) : ℤ) : K) * (-t)) *
      selectedRootElement A hd hs hp ho K (configuration.yRoot (partner (pairPick i))).val
        (((pairSign A hd hs hp ho configuration (partner (pairPick i)) : ℤ) : K) * (-t)))
  have hfirst := long_commute K (configuration.yRoot (pairPick i)).val
    (second_pairing i).1 a
    (((pairSign A hd hs hp ho configuration (pairPick i) : ℤ) : K) * (-t))
  have hpartner := long_commute K (configuration.yRoot (partner (pairPick i))).val
    (second_pairing i).2 a
    (((pairSign A hd hs hp ho configuration (partner (pairPick i)) : ℤ) : K) * (-t))
  exact hfirst.mul_right hpartner

theorem long_positive_commutes_central_scalar (K : Type) [Field K] [CharP K 2]
    (a c : K) :
    Commute (canonicalRoot realizationData K false 2 a)
      (centralMatrixHom K (Multiplicative.ofAdd (c,(0,0)))) := by
  change Commute (canonicalRoot realizationData K false 2 a)
    (centralMatrixHom K (Multiplicative.ofAdd
      (c,(0 : CFSGFFourBinaryFixedRadicalEmbedding.Extra K))))
  rw [central_scalar_word]
  exact long_commute K configuration.zRoot.val (Or.inl (by decide)) a c

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviCentralFixedAxes
