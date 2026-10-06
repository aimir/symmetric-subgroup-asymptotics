import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169PairTop
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 169: class invariant

This is a resource-bounded split of the selected action-169 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

private def representativeRows (i : Fin 7) : Fin 120 :=
  (if i.val < 3 then (if i.val < 1 then 119 else (if i.val < 2 then 45 else 35)) else (if i.val < 5 then (if i.val < 4 then 95 else 99) else (if i.val < 6 then 96 else 79)))

def representative (i : Fin 7) : Source := ⟨representativeRows i⟩

private def classCodeRows (i : Fin 120) : Fin 7 :=
  (if i.val < 60 then (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 2 else (if i.val < 2 then 2 else 1)) else (if i.val < 5 then (if i.val < 4 then 6 else 6) else (if i.val < 6 then 6 else 1))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 2 else 6) else (if i.val < 10 then 2 else 4)) else (if i.val < 13 then (if i.val < 12 then 5 else 5) else (if i.val < 14 then 5 else 4)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then 3 else (if i.val < 17 then 3 else 3)) else (if i.val < 20 then (if i.val < 19 then 5 else 3) else (if i.val < 21 then 5 else 5))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then 4 else 3) else (if i.val < 25 then 5 else 4)) else (if i.val < 28 then (if i.val < 27 then 3 else 3) else (if i.val < 29 then 5 else 3))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then 1 else (if i.val < 32 then 6 else 6)) else (if i.val < 35 then (if i.val < 34 then 6 else 2) else (if i.val < 36 then 2 else 2))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then 1 else 6) else (if i.val < 40 then 2 else 2)) else (if i.val < 43 then (if i.val < 42 then 2 else 6) else (if i.val < 44 then 6 else 6)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then 1 else (if i.val < 47 then 2 else 1)) else (if i.val < 50 then (if i.val < 49 then 6 else 2) else (if i.val < 51 then 4 else 5))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then 4 else 3) else (if i.val < 55 then 5 else 5)) else (if i.val < 58 then (if i.val < 57 then 3 else 3) else (if i.val < 59 then 3 else 5)))))) else (if i.val < 90 then (if i.val < 75 then (if i.val < 67 then (if i.val < 63 then (if i.val < 61 then 3 else (if i.val < 62 then 4 else 5)) else (if i.val < 65 then (if i.val < 64 then 5 else 5) else (if i.val < 66 then 4 else 3))) else (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then 3 else 5) else (if i.val < 70 then 3 else 6)) else (if i.val < 73 then (if i.val < 72 then 6 else 6) else (if i.val < 74 then 1 else 2)))) else (if i.val < 82 then (if i.val < 78 then (if i.val < 76 then 2 else (if i.val < 77 then 2 else 1)) else (if i.val < 80 then (if i.val < 79 then 2 else 6) else (if i.val < 81 then 6 else 2))) else (if i.val < 86 then (if i.val < 84 then (if i.val < 83 then 6 else 2) else (if i.val < 85 then 6 else 2)) else (if i.val < 88 then (if i.val < 87 then 2 else 6) else (if i.val < 89 then 1 else 1))))) else (if i.val < 105 then (if i.val < 97 then (if i.val < 93 then (if i.val < 91 then 5 else (if i.val < 92 then 3 else 3)) else (if i.val < 95 then (if i.val < 94 then 5 else 5) else (if i.val < 96 then 3 else 5))) else (if i.val < 101 then (if i.val < 99 then (if i.val < 98 then 3 else 4) else (if i.val < 100 then 4 else 3)) else (if i.val < 103 then (if i.val < 102 then 3 else 3) else (if i.val < 104 then 3 else 3)))) else (if i.val < 112 then (if i.val < 108 then (if i.val < 106 then 3 else (if i.val < 107 then 3 else 3)) else (if i.val < 110 then (if i.val < 109 then 3 else 3) else (if i.val < 111 then 1 else 2))) else (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 2 else 1) else (if i.val < 115 then 2 else 1)) else (if i.val < 118 then (if i.val < 117 then 2 else 1) else (if i.val < 119 then 1 else 0)))))))

private def classCode (x : Source) : Fin 7 := classCodeRows x.index

def classInvariant : FiniteConjugacyGeneratorInvariant ambient representative where
  Code := Fin 7
  code := classCode
  generator_invariant := by
    intro i x
    rcases x with ⟨j⟩
    fin_cases i <;> fin_cases j <;> decide +kernel
  representative_injective := by decide +kernel
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

end
