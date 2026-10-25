import SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateRootOperators
import Mathlib.Algebra.CharP.Two

/-! Selected sparse binary coefficients of the eight actual signed simple roots.
No root word or period statement is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparseRootOperators
open CFSGFFourNormCertificateRootOperators
open CFSGFFourNormCertificateCoordinates CFSGFFourE6NormQuotientOppositionLabels
open scoped BigOperators

def firstRows (neg : Bool) : Fin 4 → Fin 26 → Finset (Fin 26) :=
  if neg then ![![{14},∅,{3},∅,∅,∅,{11},∅,{12},{13},{1},∅,∅,∅,∅,{16},∅,{18},∅,∅,{21},∅,∅,∅,{25},∅],![∅,{15},∅,{4},∅,{6},∅,{8},∅,{10},∅,∅,∅,{0},{16},∅,∅,∅,{19},∅,∅,{22},∅,{24},∅,∅],![∅,∅,∅,∅,{5},∅,∅,∅,{9},∅,∅,∅,{13},∅,∅,{17},{18},∅,∅,∅,∅,∅,{23},∅,∅,∅],![∅,∅,∅,∅,∅,{7},{8},∅,∅,∅,∅,{12},∅,∅,∅,∅,∅,{20},{21},{22},∅,∅,∅,∅,∅,∅]] else ![![{10},∅,∅,{2},∅,∅,∅,∅,∅,∅,∅,{6},{8},{9},{1},∅,{15},∅,{17},∅,∅,{20},∅,∅,∅,{24}],![∅,{13},∅,∅,{3},∅,{5},∅,{7},∅,{9},∅,∅,∅,∅,{0},{14},∅,∅,{18},∅,∅,{21},∅,{23},∅],![∅,∅,∅,∅,∅,{4},∅,∅,∅,{8},∅,∅,∅,{12},∅,∅,∅,{15},{16},∅,∅,∅,∅,{22},∅,∅],![∅,∅,∅,∅,∅,∅,∅,{5},{6},∅,∅,∅,{11},∅,∅,∅,∅,∅,∅,∅,{17},{18},{19},∅,∅,∅]]

def secondRows (neg : Bool) : Fin 4 → Fin 26 → Finset (Fin 26) :=
  if neg then ![![∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{14},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅],![∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{15},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅],![∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅],![∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅]] else ![![∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{10},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅],![∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{13},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅],![∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅],![∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅]]

theorem first_mod_two : ∀ neg : Bool, ∀ i : Fin 4, ∀ j k : Fin 26,
    firstCoefficient neg i j k % 2 = if k ∈ firstRows neg i j then 1 else 0 := by
  decide +kernel

theorem second_mod_two : ∀ neg : Bool, ∀ i : Fin 4, ∀ j k : Fin 26,
    secondCoefficient neg i j k % 2 = if k ∈ secondRows neg i j then 1 else 0 := by
  decide +kernel

theorem signedCoordinate_injective (neg : Bool) : Function.Injective (signedCoordinate neg) := by
  cases neg with
  | false => exact coordinateEquiv.injective
  | true => exact negativePair_involutive.injective.comp coordinateEquiv.injective

theorem rootOperator_entry (K : Type) [CommRing K] [CharP K 2]
    (neg : Bool) (i : Fin 4) (t : K) (j k : Fin 26) :
    rootOperator K neg i t j k = (if j = k then 1 else 0) +
      t * (if k ∈ firstRows neg i j then 1 else 0) +
      t^2 * (if k ∈ secondRows neg i j then 1 else 0) := by
  have hfirst : (firstCoefficient neg i j k : K) =
      if k ∈ firstRows neg i j then 1 else 0 := by
    calc
      (firstCoefficient neg i j k : K) = ((firstCoefficient neg i j k % 2 : ℤ) : K) :=
        CharP.intCast_eq_intCast_mod K 2
      _ = _ := by
        rw [first_mod_two]
        split_ifs <;> simp only [Int.cast_one, Int.cast_zero]
  have hsecond : (secondCoefficient neg i j k : K) =
      if k ∈ secondRows neg i j then 1 else 0 := by
    calc
      (secondCoefficient neg i j k : K) = ((secondCoefficient neg i j k % 2 : ℤ) : K) :=
        CharP.intCast_eq_intCast_mod K 2
      _ = _ := by
        rw [second_mod_two]
        split_ifs <;> simp only [Int.cast_one, Int.cast_zero]
  have hdelta : signedCoordinate neg j = signedCoordinate neg k ↔ j = k :=
    (signedCoordinate_injective neg).eq_iff
  simp only [rootOperator, hfirst, hsecond, hdelta]

end SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparseRootOperators
