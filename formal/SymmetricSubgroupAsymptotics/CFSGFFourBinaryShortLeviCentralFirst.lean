import SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviRootActions
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryCentralCoordinateWords

/-! Collection of the actual two-node X-pair calculation into the same
central chart. All factors remain in their displayed selected root lines. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralFirst
open CFSGFFourBinaryShortLeviRootActions CFSGFFourBinaryCentralCoordinateWords
open CFSGFFourBinaryRadicalCentralLayers CFSGFFourE6HeisenbergLeviRoots
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalHeisenbergRootRelations
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
local instance fFourShortFirstRootsDecidableEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev U (K : Type) [CommRing K] := (Matrix Index Index K)ˣ
private abbrev px (K : Type) [CommRing K] (i : Fin 10) (t : K) : U K :=
  xHom A hd hs hp ho configuration K i (Multiplicative.ofAdd t)
private def node : Fin 2 → Fin 4 := ![0,1]

private theorem pair_indices (n : Fin 2) :
    sourceIndex n 0=pairPick n.castSucc ∧
    sourceIndex n 1=partner (pairPick n.castSucc) ∧
    targetIndex n 0=pairPick n.succ ∧
    targetIndex n 1=partner (pairPick n.succ) := by
  fin_cases n <;> decide

theorem short_positive_conjugate_pair (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (a t : K) :
    canonicalRoot realizationData K false (node n) a *
        (px K (sourceIndex n 0) t*px K (sourceIndex n 1) t) *
        (canonicalRoot realizationData K false (node n) a)⁻¹ =
      (px K (sourceIndex n 0) t*px K (sourceIndex n 1) t) *
        (px K (targetIndex n 0) (a*t)*px K (targetIndex n 1) (a*t)) := by
  let g : U K := canonicalRoot realizationData K false (node n) a
  have h0 : g*px K (sourceIndex n 0) t*g⁻¹ =
      px K (sourceIndex n 0) t*px K (targetIndex n 0) (a*t) :=
    short_positive_conjugate_first K n 0 a t
  have h1 : g*px K (sourceIndex n 1) t*g⁻¹ =
      px K (sourceIndex n 1) t*px K (targetIndex n 1) (a*t) :=
    short_positive_conjugate_first K n 1 a t
  have hc : Commute (px K (targetIndex n 0) (a*t)) (px K (sourceIndex n 1) t) :=
    x_commute A hd hs hp ho configuration K (targetIndex n 0) (sourceIndex n 1) (a*t) t
  change g*(px K (sourceIndex n 0) t*px K (sourceIndex n 1) t)*g⁻¹ = _
  calc
    _=(g*px K (sourceIndex n 0) t*g⁻¹)*(g*px K (sourceIndex n 1) t*g⁻¹) := by group
    _=(px K (sourceIndex n 0) t*px K (targetIndex n 0) (a*t))*
        (px K (sourceIndex n 1) t*px K (targetIndex n 1) (a*t)) := by rw [h0,h1]
    _=px K (sourceIndex n 0) t*(px K (targetIndex n 0) (a*t)*px K (sourceIndex n 1) t)*
        px K (targetIndex n 1) (a*t) := by group
    _=px K (sourceIndex n 0) t*(px K (sourceIndex n 1) t*px K (targetIndex n 0) (a*t))*
        px K (targetIndex n 1) (a*t) := by rw [hc.eq]
    _=_ := by group

theorem short_positive_central_first (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (a t : K) :
    canonicalRoot realizationData K false (node n) a *
        centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single n.castSucc t,0))) *
        (canonicalRoot realizationData K false (node n) a)⁻¹ =
      centralMatrixHom K (Multiplicative.ofAdd
        (0,(Pi.single n.castSucc t+Pi.single n.succ (a*t),0))) := by
  have he : (Multiplicative.ofAdd
      (0,(Pi.single n.castSucc t+Pi.single n.succ (a*t),0)) : CentralCoordinates K) =
      Multiplicative.ofAdd (0,(Pi.single n.castSucc t,0)) *
        Multiplicative.ofAdd (0,(Pi.single n.succ (a*t),0)) := by
    apply Multiplicative.toAdd.injective
    change ((0 : K),((Pi.single n.castSucc t : Fin 3 → K)+
      (Pi.single n.succ (a*t) : Fin 3 → K),(0 : Fin 3 → K))) =
      (0,((Pi.single n.castSucc t : Fin 3 → K),0))+
        (0,((Pi.single n.succ (a*t) : Fin 3 → K),0))
    apply Prod.ext
    · simp
    · apply Prod.ext <;> simp
  rw [he,map_mul,central_first_word,central_first_word]
  obtain ⟨hs0,hs1,ht0,ht1⟩ := pair_indices n
  simpa only [hs0,hs1,ht0,ht1] using short_positive_conjugate_pair K n a t

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralFirst
