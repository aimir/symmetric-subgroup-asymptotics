import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147PairTop
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 147: class invariant

This is a resource-bounded split of the selected action-147 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

private def representativeRows (i : Fin 5) : Fin 60 :=
  (if i.val < 2 then (if i.val < 1 then 59 else 17) else (if i.val < 3 then 41 else (if i.val < 4 then 22 else 39)))

def representative (i : Fin 5) : Source := ⟨representativeRows i⟩

private def classCodeRows (i : Fin 60) : Fin 5 :=
  (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 2 else (if i.val < 2 then 3 else 4)) else (if i.val < 5 then (if i.val < 4 then 2 else 4) else (if i.val < 6 then 1 else 4))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 4 else 3) else (if i.val < 10 then 1 else 4)) else (if i.val < 13 then (if i.val < 12 then 4 else 2) else (if i.val < 14 then 3 else 2)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then 3 else (if i.val < 17 then 4 else 1)) else (if i.val < 20 then (if i.val < 19 then 1 else 4) else (if i.val < 21 then 1 else 4))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then 3 else 1) else (if i.val < 25 then 4 else 2)) else (if i.val < 28 then (if i.val < 27 then 4 else 4) else (if i.val < 29 then 3 else 2))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then 4 else (if i.val < 32 then 4 else 1)) else (if i.val < 35 then (if i.val < 34 then 3 else 1) else (if i.val < 36 then 4 else 3))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then 2 else 2) else (if i.val < 40 then 4 else 4)) else (if i.val < 43 then (if i.val < 42 then 2 else 2) else (if i.val < 44 then 4 else 3)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then 1 else (if i.val < 47 then 4 else 4)) else (if i.val < 50 then (if i.val < 49 then 1 else 3) else (if i.val < 51 then 3 else 3))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then 3 else 3) else (if i.val < 55 then 3 else 2)) else (if i.val < 58 then (if i.val < 57 then 1 else 1) else (if i.val < 59 then 2 else 0))))))

private def classCode (x : Source) : Fin 5 := classCodeRows x.index

def classInvariant : FiniteConjugacyGeneratorInvariant ambient representative where
  Code := Fin 5
  code := classCode
  generator_invariant := by
    intro i x
    rcases x with ⟨j⟩
    fin_cases i <;> fin_cases j <;> decide +kernel
  representative_injective := by decide +kernel
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

end
