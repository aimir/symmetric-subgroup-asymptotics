import SymmetricSubgroupAsymptotics.CFSGFFourBinaryCentralCoordinateWords
import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergCharTwoRootRange
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroupCommute
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveRootUnits

/-! Literal unaffected central axes for the two short positive Levi
parameters. The other axes are handled by the checked active-pair and
cancelling-pair identities; no full centre action is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralFixedAxes
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGFFourE6HeisenbergLeviRoots CFSGFFourBinaryCentralCoordinateWords
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootSubgroupCommute
open CFSGFFourSerreMatrices CFSGFFourE6PositiveRootUnits CFSGSerreQuadraticMatrix
open CFSGExceptionalHeisenbergRootRelations CFSGExceptionalHeisenbergCharTwoRootRange
open CFSGExceptionalHeisenbergProduct
local instance fFourShortFixedAxesRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) :=
  Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev U (K : Type) [CommRing K] := (Matrix Index Index K)ˣ
private abbrev param (K : Type) [CommRing K] (k : Roots A) (t : K) : U K :=
  selectedRootElement A hd hs hp ho K k t
private abbrev py (K : Type) [CommRing K] (i : Fin 10) (t : K) : U K :=
  yNegative A hd hs hp ho configuration K i (Multiplicative.ofAdd t)
private def node : Fin 2 → Fin 4 := ![0,1]
private def leftIndex : Fin 2 → Fin 6 := ![0,2]
private def rightIndex : Fin 2 → Fin 6 := ![5,4]
private def fixedAxis (second : Bool) (n : Fin 2) : Fin 3 :=
  if second then n.castSucc else n.succ
private def fixedRoot (second : Bool) (n b : Fin 2) : Roots A :=
  let i := if b=0 then pairPick (fixedAxis second n) else partner (pairPick (fixedAxis second n))
  if second then (configuration.yRoot i).val else (configuration.xRoot i).val
private theorem fixed_pairings (second : Bool) (n b : Fin 2) :
    (integerPairing A (fixedRoot second n b).val
      (coordinateIndexEquiv A hd hs hp ho (leftIndex n) : Roots A).val=0 ∨
    integerPairing A (fixedRoot second n b).val
      (coordinateIndexEquiv A hd hs hp ho (leftIndex n) : Roots A).val=1) ∧
    (integerPairing A (fixedRoot second n b).val
      (coordinateIndexEquiv A hd hs hp ho (rightIndex n) : Roots A).val=0 ∨
    integerPairing A (fixedRoot second n b).val
      (coordinateIndexEquiv A hd hs hp ho (rightIndex n) : Roots A).val=1) := by
  cases second <;> fin_cases n <;> fin_cases b <;> decide
private theorem folded_commutes (K : Type) [Field K] (n : Fin 2)
    (k : Roots A)
    (hl : integerPairing A k.val (coordinateIndexEquiv A hd hs hp ho (leftIndex n) : Roots A).val=0 ∨
      integerPairing A k.val (coordinateIndexEquiv A hd hs hp ho (leftIndex n) : Roots A).val=1)
    (hr : integerPairing A k.val (coordinateIndexEquiv A hd hs hp ho (rightIndex n) : Roots A).val=0 ∨
      integerPairing A k.val (coordinateIndexEquiv A hd hs hp ho (rightIndex n) : Roots A).val=1)
    (a t : K) : Commute (canonicalRoot realizationData K false (node n) a) (param K k t) := by
  have hleft := (rootSubgroup_pair_commute A hd hs hp ho K k
    (coordinateIndexEquiv A hd hs hp ho (leftIndex n)) hl _ _
    (selectedRootElement_mem A hd hs hp ho K k t)
    (canonicalRoot_mem_rootSubgroup A hd hs hp ho K (leftIndex n) a)).symm
  have hright := (rootSubgroup_pair_commute A hd hs hp ho K k
    (coordinateIndexEquiv A hd hs hp ho (rightIndex n)) hr _ _
    (selectedRootElement_mem A hd hs hp ho K k t)
    (canonicalRoot_mem_rootSubgroup A hd hs hp ho K (rightIndex n) a)).symm
  have hfold : canonicalRoot realizationData K false (node n) a =
      canonicalRoot e6Data K false (leftIndex n) a *
        canonicalRoot e6Data K false (rightIndex n) a := by
    fin_cases n <;> rw [folded_positive_root] <;> rfl
  rw [hfold]
  exact hleft.mul_left hright

theorem short_positive_commutes_central_first (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (a t : K) :
    Commute (canonicalRoot realizationData K false (node n) a)
      (centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single n.succ t,0)))) := by
  rw [central_first_word]
  change Commute (canonicalRoot realizationData K false (node n) a)
    (param K (fixedRoot false n 0) t * param K (fixedRoot false n 1) t)
  have hfirst := folded_commutes K n (fixedRoot false n 0)
    (fixed_pairings false n 0).1 (fixed_pairings false n 0).2 a t
  have hpartner := folded_commutes K n (fixedRoot false n 1)
    (fixed_pairings false n 1).1 (fixed_pairings false n 1).2 a t
  exact hfirst.mul_right hpartner

theorem short_positive_commutes_central_second (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (a t : K) :
    Commute (canonicalRoot realizationData K false (node n) a)
      (centralMatrixHom K (Multiplicative.ofAdd (0,(0,Pi.single n.castSucc t)))) := by
  have hy (i : Fin 10) : py K i t=param K (configuration.yRoot i).val t :=
    DFunLike.congr_fun (yNegative_eq_selectedRootHom A hd hs hp ho configuration K i)
      (Multiplicative.ofAdd t)
  rw [central_second_word]
  change Commute (canonicalRoot realizationData K false (node n) a)
    (py K (pairPick n.castSucc) t * py K (partner (pairPick n.castSucc)) t)
  rw [hy,hy]
  have hfirst := folded_commutes K n (fixedRoot true n 0)
    (fixed_pairings true n 0).1 (fixed_pairings true n 0).2 a t
  have hpartner := folded_commutes K n (fixedRoot true n 1)
    (fixed_pairings true n 1).1 (fixed_pairings true n 1).2 a t
  exact hfirst.mul_right hpartner

theorem short_positive_commutes_central_scalar (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (a c : K) :
    Commute (canonicalRoot realizationData K false (node n) a)
      (centralMatrixHom K (Multiplicative.ofAdd (c,(0,0)))) := by
  change Commute (canonicalRoot realizationData K false (node n) a)
    (centralMatrixHom K (Multiplicative.ofAdd
      (c,(0 : CFSGFFourBinaryFixedRadicalEmbedding.Extra K))))
  rw [central_scalar_word]
  apply folded_commutes K n configuration.zRoot.val
  · fin_cases n <;> decide
  · fin_cases n <;> decide

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralFixedAxes
