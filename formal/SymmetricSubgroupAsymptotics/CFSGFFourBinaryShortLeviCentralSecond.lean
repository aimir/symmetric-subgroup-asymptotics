import SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviSecondRootActions
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryCentralCoordinateWords

/-! Collection of the actual two-node Y-pair calculation into the same
central chart. All factors remain in their displayed selected root lines. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralSecond
open CFSGFFourBinaryShortLeviRootActions CFSGFFourBinaryShortLeviSecondRootActions
open CFSGFFourBinaryCentralCoordinateWords CFSGExceptionalHeisenbergProduct
open CFSGFFourBinaryRadicalCentralLayers CFSGFFourE6HeisenbergLeviRoots
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalHeisenbergRootRelations
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
local instance fFourShortSecondPairRootsDecidableEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev U (K : Type) [CommRing K] := (Matrix Index Index K)ˣ
private abbrev py (K : Type) [CommRing K] (i : Fin 10) (t : K) : U K :=
  yNegative A hd hs hp ho configuration K i (Multiplicative.ofAdd t)
private def node : Fin 2 → Fin 4 := ![0,1]

private theorem pair_indices (n : Fin 2) :
    sourceIndex n 0=pairPick n.castSucc ∧
    sourceIndex n 1=partner (pairPick n.castSucc) ∧
    targetIndex n 0=pairPick n.succ ∧
    targetIndex n 1=partner (pairPick n.succ) := by
  fin_cases n <;> decide

theorem short_positive_conjugate_second_pair (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (a t : K) :
    canonicalRoot realizationData K false (node n) a *
        (py K (targetIndex n 0) t*py K (targetIndex n 1) t) *
        (canonicalRoot realizationData K false (node n) a)⁻¹ =
      (py K (targetIndex n 0) t*py K (targetIndex n 1) t) *
        (py K (sourceIndex n 0) (a*t)*py K (sourceIndex n 1) (a*t)) := by
  let g : U K := canonicalRoot realizationData K false (node n) a
  have h0 : g*py K (targetIndex n 0) t*g⁻¹ =
      py K (targetIndex n 0) t*py K (sourceIndex n 0) (a*t) :=
    short_positive_conjugate_second K n 0 a t
  have h1 : g*py K (targetIndex n 1) t*g⁻¹ =
      py K (targetIndex n 1) t*py K (sourceIndex n 1) (a*t) :=
    short_positive_conjugate_second K n 1 a t
  have hc : Commute (py K (sourceIndex n 0) (a*t)) (py K (targetIndex n 1) t) :=
    y_commute A hd hs hp ho configuration K (sourceIndex n 0) (targetIndex n 1) (-(a*t)) (-t)
  change g*(py K (targetIndex n 0) t*py K (targetIndex n 1) t)*g⁻¹ = _
  calc
    _=(g*py K (targetIndex n 0) t*g⁻¹)*(g*py K (targetIndex n 1) t*g⁻¹) := by group
    _=(py K (targetIndex n 0) t*py K (sourceIndex n 0) (a*t))*
        (py K (targetIndex n 1) t*py K (sourceIndex n 1) (a*t)) := by rw [h0,h1]
    _=py K (targetIndex n 0) t*(py K (sourceIndex n 0) (a*t)*py K (targetIndex n 1) t)*
        py K (sourceIndex n 1) (a*t) := by group
    _=py K (targetIndex n 0) t*(py K (targetIndex n 1) t*py K (sourceIndex n 0) (a*t))*
        py K (sourceIndex n 1) (a*t) := by rw [hc.eq]
    _=_ := by group

theorem short_positive_central_second (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (a t : K) :
    canonicalRoot realizationData K false (node n) a *
        centralMatrixHom K (Multiplicative.ofAdd (0,(0,Pi.single n.succ t))) *
        (canonicalRoot realizationData K false (node n) a)⁻¹ =
      centralMatrixHom K (Multiplicative.ofAdd
        (0,(0,Pi.single n.succ t+Pi.single n.castSucc (a*t)))) := by
  have he : (Multiplicative.ofAdd
      (0,(0,Pi.single n.succ t+Pi.single n.castSucc (a*t))) : CentralCoordinates K) =
      Multiplicative.ofAdd (0,(0,Pi.single n.succ t)) *
        Multiplicative.ofAdd (0,(0,Pi.single n.castSucc (a*t))) := by
    apply Multiplicative.toAdd.injective
    change ((0 : K),((0 : Fin 3 → K),(Pi.single n.succ t : Fin 3 → K)+
      (Pi.single n.castSucc (a*t) : Fin 3 → K))) =
      (0,(0,(Pi.single n.succ t : Fin 3 → K)))+
        (0,(0,(Pi.single n.castSucc (a*t) : Fin 3 → K)))
    apply Prod.ext
    · simp
    · apply Prod.ext <;> simp
  rw [he,map_mul,central_second_word,central_second_word K n.castSucc (a*t)]
  obtain ⟨hs0,hs1,ht0,ht1⟩ := pair_indices n
  simpa only [hs0,hs1,ht0,ht1] using short_positive_conjugate_second_pair K n a t

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralSecond
