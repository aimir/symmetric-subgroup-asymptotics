import SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergLeviRoots

/-! Closure certificates for the already displayed twenty-one radical
root generators under the five head-zero simple steps. These assertions
only concern the selected configuration, not an enumeration of E6 roots
or a recognition premise for an actual subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergLeviRootClosure
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6HeisenbergStableRootFamilies
private abbrev Label := Fin 10 ⊕ (Fin 10 ⊕ Unit)
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def radicalRoot : Label → Roots A
  | .inl i => (configuration.xRoot i).val
  | .inr (.inl i) => (configuration.yRoot i).val
  | .inr (.inr _) => configuration.zRoot.val

def leviSimple : Fin 5 → Fin 6 := ![0,2,3,4,5]

theorem positive_step_closed (b : Label) (i : Fin 5) :
    integerPairing A (radicalRoot b).val
        (coordinateIndexEquiv A hd hs hp ho (leviSimple i) : Roots A).val=0 ∨
    integerPairing A (radicalRoot b).val
        (coordinateIndexEquiv A hd hs hp ho (leviSimple i) : Roots A).val=1 ∨
    (integerPairing A (radicalRoot b).val
        (coordinateIndexEquiv A hd hs hp ho (leviSimple i) : Roots A).val= -1 ∧
      ∃ c : Label, (radicalRoot c).val = (radicalRoot b).val+
        (coordinateIndexEquiv A hd hs hp ho (leviSimple i) : Roots A).val) := by
  rcases b with b | (b | b)
  · fin_cases b <;> fin_cases i <;> decide
  · fin_cases b <;> fin_cases i <;> decide
  · cases b
    fin_cases i <;> decide

theorem reflection_step_closed (b : Label) (i : Fin 5) :
    ∃ c : Label, (radicalRoot c).val = (radicalRoot b).val-
      integerPairing A (radicalRoot b).val
        (coordinateIndexEquiv A hd hs hp ho (leviSimple i) : Roots A).val •
          (coordinateIndexEquiv A hd hs hp ho (leviSimple i) : Roots A).val := by
  rcases b with b | (b | b)
  · fin_cases b <;> fin_cases i <;> decide
  · fin_cases b <;> fin_cases i <;> decide
  · cases b
    fin_cases i <;> decide

end SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergLeviRootClosure
