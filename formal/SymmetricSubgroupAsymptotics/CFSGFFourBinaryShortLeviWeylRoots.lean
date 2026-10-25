import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviWeylNormalizer
import SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergLeviRoots

/-! Literal short-Levi Weyl transport on the paired central roots. The
unaffected pair is reversed internally; the two active pairs are swapped.
Only these displayed roots are checked, and the actual parameter identity
comes from the original signed integral word transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviWeylRoots
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGFFourE6HeisenbergLeviRoots
open CFSGFFourE6RelativeWords CFSGFFourE6PositiveRootUnits
open CFSGNormTwoCoordinateWordRootElementSign CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateSelectedRootElement CFSGTwistedE6RelativeWeylOrbits
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
local instance fFourShortWeylRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev U (K : Type) [CommRing K] := (Matrix Index Index K)ˣ
private abbrev param (K : Type) [CommRing K] (k : Roots A) (t : K) : U K :=
  selectedRootElement A hd hs hp ho K k t
private def node : Fin 2 → Fin 4 := ![0,1]

def pairedRoot (second : Bool) (i : Fin 3) (b : Fin 2) : Roots A :=
  let j := if b=0 then pairPick i else partner (pairPick i)
  if second then (configuration.yRoot j).val else (configuration.xRoot j).val

def swapIndex (n : Fin 2) : Equiv.Perm (Fin 3) := Equiv.swap n.castSucc n.succ

def swapFactor (n : Fin 2) (i : Fin 3) (b : Fin 2) : Fin 2 :=
  if i=(![2,0] : Fin 2 → Fin 3) n then b.rev else b

private def latticeWord : List (Fin 6) → (Fin 6 → ℤ) → (Fin 6 → ℤ)
  | [],v => v
  | j::w,v => latticeWord w v -
      integerPairing A (latticeWord w v) (Pi.single j (1 : ℤ)) • Pi.single j (1 : ℤ)
private theorem wordRoot_val (w : List (Fin 6)) (k : Roots A) :
    (wordRoot A hs hp (coordinateBase A hd hs hp ho)
      (coordinateIndexEquiv A hd hs hp ho) w k).val = latticeWord w k.val := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change (wordRoot A hs hp (coordinateBase A hd hs hp ho)
        (coordinateIndexEquiv A hd hs hp ho) w k).val -
      integerPairing A (wordRoot A hs hp (coordinateBase A hd hs hp ho)
        (coordinateIndexEquiv A hd hs hp ho) w k).val (Pi.single j (1 : ℤ)) •
        Pi.single j (1 : ℤ) = latticeWord (j::w) k.val
    rw [ih]
    rfl

theorem short_word_root (second : Bool) (n : Fin 2) (i : Fin 3) (b : Fin 2) :
    wordRoot A hs hp (coordinateBase A hd hs hp ho)
      (coordinateIndexEquiv A hd hs hp ho) (orbitWord (node n)) (pairedRoot second i b) =
        pairedRoot second (swapIndex n i) (swapFactor n i b) := by
  apply Subtype.ext
  rw [wordRoot_val]
  cases second <;> fin_cases n <;> fin_cases i <;> fin_cases b <;> decide

theorem short_weyl_conjugate_root (K : Type) [Field K] [CharP K 2]
    (second : Bool) (n : Fin 2) (i : Fin 3) (b : Fin 2) (t : K) :
    canonicalWeyl realizationData K (node n) * param K (pairedRoot second i b) t *
      (canonicalWeyl realizationData K (node n))⁻¹ =
        param K (pairedRoot second (swapIndex n i) (swapFactor n i b)) t := by
  obtain ⟨e,he,htransport⟩ := word_selected_root_sign A hd hs hp ho
    (orbitWord (node n)) (pairedRoot second i b)
  have hsign : (e : K)=1 := by
    rcases he with rfl | rfl <;> simp only [Int.cast_one,Int.cast_neg,CharTwo.neg_eq]
  have ht := htransport K t
  rw [short_word_root,hsign,one_mul] at ht
  rw [foldedWeyl_eq_orbitWord]
  exact ht

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviWeylRoots
