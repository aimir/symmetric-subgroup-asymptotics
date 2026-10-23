import SymmetricSubgroupAsymptotics.CFSGFFourE6RegularPositive
import SymmetricSubgroupAsymptotics.CFSGFFourE6DiagramFixed
import Mathlib.SetTheory.Cardinal.Finite

/-! The first fixed-height chart is an actual four-parameter word in the
folded positive F4 subgroup. Ambient E6 leading coordinates recover every
parameter, including in characteristics two and three. This is a chart
in the matrix subgroup, not a claim that the original source is faithful. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleParameters
open CFSGFFourSerreMatrices CFSGFFourE6RootSubgroups CFSGFFourE6PositiveRootUnits
open CFSGFFourE6RegularPositive CFSGFFourE6DiagramFixed
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor
open CFSGSerreQuadraticMatrix

private def e6Root (K : Type) [Field K] (i : Fin 6) (a : K) : E6Positive K :=
  positiveRoot CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K i a

def ambientWord (K : Type) [Field K] (a : Fin 4 → K) : E6Positive K :=
  e6Root K 0 (a 0) * e6Root K 5 (a 0) *
    e6Root K 2 (a 1) * e6Root K 4 (a 1) *
    e6Root K 3 (a 2) * e6Root K 1 (a 3)

def foldedWord (K : Type) [Field K] (a : Fin 4 → K) :
    (Matrix Index Index K)ˣ :=
  canonicalRoot realizationData K false 0 (a 0) *
    canonicalRoot realizationData K false 1 (a 1) *
    canonicalRoot realizationData K false 2 (a 2) *
    canonicalRoot realizationData K false 3 (a 3)

theorem ambientWord_val (K : Type) [Field K] (a : Fin 4 → K) :
    (ambientWord K a).val = foldedWord K a := by
  simp only [foldedWord, folded_positive_root]
  change canonicalRoot e6Data K false 0 (a 0) * canonicalRoot e6Data K false 5 (a 0) *
      canonicalRoot e6Data K false 2 (a 1) * canonicalRoot e6Data K false 4 (a 1) *
      canonicalRoot e6Data K false 3 (a 2) * canonicalRoot e6Data K false 1 (a 3) =
    (canonicalRoot e6Data K false 0 (a 0) * canonicalRoot e6Data K false 5 (a 0)) *
      (canonicalRoot e6Data K false 2 (a 1) * canonicalRoot e6Data K false 4 (a 1)) *
      canonicalRoot e6Data K false 3 (a 2) * canonicalRoot e6Data K false 1 (a 3)
  simp only [mul_assoc]

theorem foldedWord_mem (K : Type) [Field K] (a : Fin 4 → K) :
    foldedWord K a ∈ foldedRootGroup K false := by
  exact (foldedRootGroup K false).mul_mem
    ((foldedRootGroup K false).mul_mem
      ((foldedRootGroup K false).mul_mem (folded_root_mem K false 0 (a 0))
        (folded_root_mem K false 1 (a 1))) (folded_root_mem K false 2 (a 2)))
      (folded_root_mem K false 3 (a 3))

theorem ambientWord_leading (K : Type) [Field K] (a : Fin 4 → K) :
    leadingCoordinates CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (ambientWord K a).val =
      ![a 0, a 3, a 1, a 2, a 1, a 0] := by
  let L : E6Positive K →* Multiplicative (Fin 6 → K) :=
    leadingHom CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K
  have hr (i : Fin 6) (t : K) : L (e6Root K i t) =
      Multiplicative.ofAdd (Pi.single i t : Fin 6 → K) :=
    leadingHom_positiveRoot CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K i t
  have hw : L (ambientWord K a) =
      Multiplicative.ofAdd (Pi.single 0 (a 0) + Pi.single 5 (a 0) + Pi.single 2 (a 1) +
        Pi.single 4 (a 1) + Pi.single 3 (a 2) + Pi.single 1 (a 3) : Fin 6 → K) := by
    change L (e6Root K 0 (a 0) * e6Root K 5 (a 0) *
      e6Root K 2 (a 1) * e6Root K 4 (a 1) *
      e6Root K 3 (a 2) * e6Root K 1 (a 3)) = _
    rw [L.map_mul,L.map_mul,L.map_mul,L.map_mul,L.map_mul,
      hr,hr,hr,hr,hr,hr]
    rfl
  have ha := congrArg Multiplicative.toAdd hw
  change leadingCoordinates CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (ambientWord K a).val = _ at ha
  rw [ha]
  funext i
  fin_cases i <;> simp

theorem foldedWord_injective (K : Type) [Field K] :
    Function.Injective (foldedWord K) := by
  intro a b hab
  have hv : (ambientWord K a).val = (ambientWord K b).val :=
    (ambientWord_val K a).trans (hab.trans (ambientWord_val K b).symm)
  have hc := congrArg
    (leadingCoordinates CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K) hv
  rw [ambientWord_leading, ambientWord_leading] at hc
  have h0 := congrFun hc (0 : Fin 6)
  have h1 := congrFun hc (2 : Fin 6)
  have h2 := congrFun hc (3 : Fin 6)
  have h3 := congrFun hc (1 : Fin 6)
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3

def positiveChart (K : Type) [Field K] (a : Fin 4 → K) : foldedRootGroup K false :=
  ⟨foldedWord K a, foldedWord_mem K a⟩

theorem positiveChart_injective (K : Type) [Field K] :
    Function.Injective (positiveChart K) := by
  intro a b hab
  exact foldedWord_injective K (congrArg Subtype.val hab)

theorem positive_card_lower_four (K : Type) [Field K] [Finite K] :
    Nat.card K ^ 4 ≤ Nat.card (foldedRootGroup K false) := by
  have h := Nat.card_le_card_of_injective (positiveChart K) (positiveChart_injective K)
  simpa only [Nat.card_fun, Nat.card_fin] using h

end SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleParameters
