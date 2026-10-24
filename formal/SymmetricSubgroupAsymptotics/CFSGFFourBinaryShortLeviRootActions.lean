import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoSimpleConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroupCommute
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviRootActions

/-! The two folded short positive Levi parameters act on their two
selected X factors by actual root-word raising. This is a small uniform
two-node pilot; no action on the full centre or radical is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviRootActions
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGExceptionalHeisenbergRootRelations CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6PositiveRootUnits CFSGNormTwoCoordinateRaisedRoot
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootSubgroupCommute
local instance fFourShortLeviRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev U (K : Type) [CommRing K] := (Matrix Index Index K)ˣ
private abbrev px (K : Type) [CommRing K] (i : Fin 10) (t : K) : U K :=
  xHom A hd hs hp ho configuration K i (Multiplicative.ofAdd t)
private abbrev simple (K : Type) [CommRing K] (i : Fin 6) (a : K) : U K :=
  canonicalRoot e6Data K false i a

def sourceIndex (n b : Fin 2) : Fin 10 := ![![2,4],![3,9]] n b
def targetIndex (n b : Fin 2) : Fin 10 := ![![3,9],![6,8]] n b
private def leftIndex : Fin 2 → Fin 6 := ![0,2]
private def rightIndex : Fin 2 → Fin 6 := ![5,4]
private def raisingIndex (n b : Fin 2) : Fin 6 := if n=b then rightIndex n else leftIndex n
private def otherIndex (n b : Fin 2) : Fin 6 := if n=b then leftIndex n else rightIndex n
private def foldedIndex : Fin 2 → Fin 4 := ![0,1]

private theorem raising_pairing (n b : Fin 2) :
    integerPairing A (configuration.x (sourceIndex n b))
      (coordinateIndexEquiv A hd hs hp ho (raisingIndex n b) : Roots A).val= -1 := by
  fin_cases n <;> fin_cases b <;> decide
private theorem raised_target (n b : Fin 2) :
    raisedRoot A hd hs hp ho (configuration.xRoot (sourceIndex n b)).val
      (raisingIndex n b) (raising_pairing n b) = (configuration.xRoot (targetIndex n b)).val := by
  apply Subtype.ext
  change configuration.x (sourceIndex n b)+Pi.single (raisingIndex n b) (1 : ℤ) =
    configuration.x (targetIndex n b)
  fin_cases n <;> fin_cases b <;> decide
private theorem other_pairing (n b : Fin 2) :
    integerPairing A (configuration.x (sourceIndex n b))
      (coordinateIndexEquiv A hd hs hp ho (otherIndex n b) : Roots A).val=0 ∧
    integerPairing A (configuration.x (targetIndex n b))
      (coordinateIndexEquiv A hd hs hp ho (otherIndex n b) : Roots A).val=0 := by
  fin_cases n <;> fin_cases b <;> decide

private theorem simple_commutes (K : Type) [Field K] (k : Roots A) (j : Fin 6)
    (hk : integerPairing A k.val (coordinateIndexEquiv A hd hs hp ho j : Roots A).val=0)
    (a t : K) : Commute (simple K j a) (selectedRootElement A hd hs hp ho K k t) :=
  (rootSubgroup_pair_commute A hd hs hp ho K k (coordinateIndexEquiv A hd hs hp ho j)
    (Or.inl hk) _ _ (selectedRootElement_mem A hd hs hp ho K k t)
    (canonicalRoot_mem_rootSubgroup A hd hs hp ho K j a)).symm

private theorem raising_action (K : Type) [Field K] [CharP K 2]
    (n b : Fin 2) (a t : K) :
    simple K (raisingIndex n b) a*px K (sourceIndex n b) t*
      (simple K (raisingIndex n b) a)⁻¹ =
      px K (sourceIndex n b) t*px K (targetIndex n b) (a*t) := by
  have h := CFSGNormTwoCoordinateCharTwoSimpleConjugation.simple_positive_conjugate
    A hd hs hp ho K (configuration.xRoot (sourceIndex n b)).val
    (configuration.positive_x (sourceIndex n b)) (raisingIndex n b) (raising_pairing n b) a t
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

theorem short_positive_conjugate_first (K : Type) [Field K] [CharP K 2]
    (n b : Fin 2) (a t : K) :
    canonicalRoot realizationData K false (foldedIndex n) a * px K (sourceIndex n b) t *
      (canonicalRoot realizationData K false (foldedIndex n) a)⁻¹ =
      px K (sourceIndex n b) t*px K (targetIndex n b) (a*t) := by
  have hx := simple_commutes K (configuration.xRoot (sourceIndex n b)).val
    (otherIndex n b) (other_pairing n b).1 a t
  have hy := simple_commutes K (configuration.xRoot (targetIndex n b)).val
    (otherIndex n b) (other_pairing n b).2 a (a*t)
  have h := two_conjugations (simple K (raisingIndex n b) a) (simple K (otherIndex n b) a)
    (px K (sourceIndex n b) t) (px K (targetIndex n b) (a*t)) (raising_action K n b a t) hx hy
  have hfold : canonicalRoot realizationData K false (foldedIndex n) a =
      simple K (leftIndex n) a*simple K (rightIndex n) a := by
    fin_cases n <;> rw [folded_positive_root] <;> rfl
  rw [hfold]
  by_cases hb : n=b
  · simpa only [raisingIndex,otherIndex,if_pos hb] using h.2
  · simpa only [raisingIndex,otherIndex,if_neg hb] using h.1

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviRootActions
