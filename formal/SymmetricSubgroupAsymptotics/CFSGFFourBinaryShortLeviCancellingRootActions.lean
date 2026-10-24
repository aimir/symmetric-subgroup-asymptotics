import SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviRootActions

/-! The remaining paired axes have duplicate raised-root contributions.
This pilot retains the actual selected source and result roots for all
four cases; cancellation of the two parameter factors is a later step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCancellingRootActions
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix CFSGFFourE6PositiveRootUnits
open CFSGNormTwoCoordinateRaisedRoot CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateRootSubgroupCommute
local instance fFourCancellingRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev U (K : Type) [CommRing K] := (Matrix Index Index K)ˣ
private abbrev param (K : Type) [CommRing K] (k : Roots A) (t : K) : U K :=
  selectedRootElement A hd hs hp ho K k t
private abbrev simple (K : Type) [CommRing K] (i : Fin 6) (a : K) : U K :=
  canonicalRoot e6Data K false i a
private def extraIndex (n b : Fin 2) : Fin 10 := ![![6,8],![2,4]] n b

def sourceRoot (second : Bool) (n b : Fin 2) : PositiveRoot A :=
  if second then configuration.yRoot (extraIndex n b) else configuration.xRoot (extraIndex n b)

def resultRoot (second : Bool) (n : Fin 2) : PositiveRoot A :=
  if second then configuration.yRoot ((![5,1] : Fin 2 → Fin 10) n)
  else if n=0 then configuration.yRoot 7 else configuration.xRoot 5

private def leftIndex : Fin 2 → Fin 6 := ![0,2]
private def rightIndex : Fin 2 → Fin 6 := ![5,4]
private def raisingIndex (second : Bool) (n b : Fin 2) : Fin 6 :=
  if b=(if second then 1 else 0) then leftIndex n else rightIndex n
private def otherIndex (second : Bool) (n b : Fin 2) : Fin 6 :=
  if b=(if second then 1 else 0) then rightIndex n else leftIndex n
private def foldedIndex : Fin 2 → Fin 4 := ![0,1]

private theorem raising_pairing (second : Bool) (n b : Fin 2) :
    integerPairing A (sourceRoot second n b).val.val
      (coordinateIndexEquiv A hd hs hp ho (raisingIndex second n b) : Roots A).val= -1 := by
  cases second <;> fin_cases n <;> fin_cases b <;> decide
private theorem raised_target (second : Bool) (n b : Fin 2) :
    raisedRoot A hd hs hp ho (sourceRoot second n b).val
      (raisingIndex second n b) (raising_pairing second n b) = (resultRoot second n).val := by
  apply Subtype.ext
  change (sourceRoot second n b).val.val+
    (Pi.single (raisingIndex second n b) (1 : ℤ) : Fin 6 → ℤ) =
    (resultRoot second n).val.val
  cases second <;> fin_cases n <;> fin_cases b <;> decide
private theorem other_pairing (second : Bool) (n b : Fin 2) :
    integerPairing A (sourceRoot second n b).val.val
      (coordinateIndexEquiv A hd hs hp ho (otherIndex second n b) : Roots A).val=1 ∧
    integerPairing A (resultRoot second n).val.val
      (coordinateIndexEquiv A hd hs hp ho (otherIndex second n b) : Roots A).val=1 := by
  cases second <;> fin_cases n <;> fin_cases b <;> decide

private theorem simple_commutes (K : Type) [Field K] (k : Roots A) (j : Fin 6)
    (hk : integerPairing A k.val (coordinateIndexEquiv A hd hs hp ho j : Roots A).val=1)
    (a t : K) : Commute (simple K j a) (param K k t) :=
  (rootSubgroup_pair_commute A hd hs hp ho K k (coordinateIndexEquiv A hd hs hp ho j)
    (Or.inr hk) _ _ (selectedRootElement_mem A hd hs hp ho K k t)
    (canonicalRoot_mem_rootSubgroup A hd hs hp ho K j a)).symm

private theorem raising_action (K : Type) [Field K] [CharP K 2]
    (second : Bool) (n b : Fin 2) (a t : K) :
    simple K (raisingIndex second n b) a*param K (sourceRoot second n b).val t*
      (simple K (raisingIndex second n b) a)⁻¹ =
      param K (sourceRoot second n b).val t*param K (resultRoot second n).val (a*t) := by
  have h := CFSGNormTwoCoordinateCharTwoSimpleConjugation.simple_positive_conjugate
    A hd hs hp ho K (sourceRoot second n b).val (sourceRoot second n b).property
    (raisingIndex second n b) (raising_pairing second n b) a t
  rw [raised_target] at h
  exact h

private theorem two_conjugations {G : Type} [Group G] (g h x y : G)
    (hstep : g*x*g⁻¹=x*y) (hx : Commute h x) (hy : Commute h y) :
    (g*h)*x*(g*h)⁻¹=x*y ∧ (h*g)*x*(h*g)⁻¹=x*y := by
  have hfixx : h*x*h⁻¹=x := by rw [hx.eq]; group
  have hfixy : h*y*h⁻¹=y := by rw [hy.eq]; group
  constructor
  · calc
      _=g*(h*x*h⁻¹)*g⁻¹ := by group
      _=g*x*g⁻¹ := by rw [hfixx]
      _=x*y := hstep
  · calc
      _=h*(g*x*g⁻¹)*h⁻¹ := by group
      _=h*(x*y)*h⁻¹ := by rw [hstep]
      _=(h*x*h⁻¹)*(h*y*h⁻¹) := by group
      _=x*y := by rw [hfixx,hfixy]

theorem short_positive_conjugate_cancelling_root (K : Type) [Field K] [CharP K 2]
    (second : Bool) (n b : Fin 2) (a t : K) :
    canonicalRoot realizationData K false (foldedIndex n) a *
        param K (sourceRoot second n b).val t *
        (canonicalRoot realizationData K false (foldedIndex n) a)⁻¹ =
      param K (sourceRoot second n b).val t*param K (resultRoot second n).val (a*t) := by
  have hx := simple_commutes K (sourceRoot second n b).val
    (otherIndex second n b) (other_pairing second n b).1 a t
  have hy := simple_commutes K (resultRoot second n).val
    (otherIndex second n b) (other_pairing second n b).2 a (a*t)
  have h := two_conjugations (simple K (raisingIndex second n b) a)
    (simple K (otherIndex second n b) a) (param K (sourceRoot second n b).val t)
    (param K (resultRoot second n).val (a*t)) (raising_action K second n b a t) hx hy
  have hfold : canonicalRoot realizationData K false (foldedIndex n) a =
      simple K (leftIndex n) a*simple K (rightIndex n) a := by
    fin_cases n <;> rw [folded_positive_root] <;> rfl
  rw [hfold]
  by_cases hb : b=(if second then 1 else 0)
  · simpa only [raisingIndex,otherIndex,if_pos hb] using h.1
  · simpa only [raisingIndex,otherIndex,if_neg hb] using h.2

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCancellingRootActions
