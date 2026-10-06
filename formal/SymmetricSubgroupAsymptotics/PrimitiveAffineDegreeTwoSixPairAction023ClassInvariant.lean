import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023PairTop
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 23: class invariant

This is a resource-bounded split of the selected action-23 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023ClassPilot

private def representativeRows (i : Fin 4) : Fin 12 :=
  (if i.val < 2 then (if i.val < 1 then 11 else 5) else (if i.val < 3 then 6 else 2))

def representative (i : Fin 4) : Source := ⟨representativeRows i⟩

private def classCodeRows (i : Fin 12) : Fin 4 :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 2 else (if i.val < 2 then 2 else 3)) else (if i.val < 4 then 3 else (if i.val < 5 then 1 else 1))) else (if i.val < 9 then (if i.val < 7 then 2 else (if i.val < 8 then 2 else 3)) else (if i.val < 10 then 3 else (if i.val < 11 then 1 else 0))))

private def classCode (x : Source) : Fin 4 := classCodeRows x.index

def classInvariant : FiniteConjugacyGeneratorInvariant ambient representative where
  Code := Fin 4
  code := classCode
  generator_invariant := by
    intro i x
    rcases x with ⟨j⟩
    fin_cases i <;> fin_cases j <;> decide +kernel
  representative_injective := by decide +kernel
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023ClassPilot

end
