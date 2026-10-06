import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassInvariant
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 169: centralizer row 0

This is a resource-bounded split of the selected action-169 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

namespace C0

private def kernelRows (_j : Fin 1) : Fin 120 :=
  119

private def topRows (j : Fin 120) : Fin 120 :=
  (if j.val < 60 then (if j.val < 30 then (if j.val < 15 then (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 119 else (if j.val < 2 then 95 else 69)) else (if j.val < 5 then (if j.val < 4 then 45 else 89) else (if j.val < 6 then 103 else 35))) else (if j.val < 11 then (if j.val < 9 then (if j.val < 8 then 67 else 57) else (if j.val < 10 then 29 else 115)) else (if j.val < 13 then (if j.val < 12 then 83 else 107) else (if j.val < 14 then 73 else 49)))) else (if j.val < 22 then (if j.val < 18 then (if j.val < 16 then 23 else (if j.val < 17 then 75 else 97)) else (if j.val < 20 then (if j.val < 19 then 37 else 53) else (if j.val < 21 then 117 else 99))) else (if j.val < 26 then (if j.val < 24 then (if j.val < 23 then 65 else 47) else (if j.val < 25 then 79 else 7)) else (if j.val < 28 then (if j.val < 27 then 101 else 96) else (if j.val < 29 then 109 else 81))))) else (if j.val < 45 then (if j.val < 37 then (if j.val < 33 then (if j.val < 31 then 48 else (if j.val < 32 then 13 else 55)) else (if j.val < 35 then (if j.val < 34 then 19 else 114) else (if j.val < 36 then 71 else 85))) else (if j.val < 41 then (if j.val < 39 then (if j.val < 38 then 66 else 51) else (if j.val < 40 then 5 else 87)) else (if j.val < 43 then (if j.val < 42 then 108 else 39) else (if j.val < 44 then 63 else 77)))) else (if j.val < 52 then (if j.val < 48 then (if j.val < 46 then 9 else (if j.val < 47 then 106 else 91)) else (if j.val < 50 then (if j.val < 49 then 98 else 111) else (if j.val < 51 then 11 else 36))) else (if j.val < 56 then (if j.val < 54 then (if j.val < 53 then 113 else 68) else (if j.val < 55 then 21 else 4)) else (if j.val < 58 then (if j.val < 57 then 25 else 17) else (if j.val < 59 then 82 else 70)))))) else (if j.val < 90 then (if j.val < 75 then (if j.val < 67 then (if j.val < 63 then (if j.val < 61 then 59 else (if j.val < 62 then 27 else 112)) else (if j.val < 65 then (if j.val < 64 then 84 else 105) else (if j.val < 66 then 88 else 41))) else (if j.val < 71 then (if j.val < 69 then (if j.val < 68 then 16 else 93) else (if j.val < 70 then 118 else 18)) else (if j.val < 73 then (if j.val < 72 then 31 else 38) else (if j.val < 74 then 3 else 100)))) else (if j.val < 82 then (if j.val < 78 then (if j.val < 76 then 52 else (if j.val < 77 then 46 else 90)) else (if j.val < 80 then (if j.val < 79 then 1 else 22) else (if j.val < 81 then 104 else 78))) else (if j.val < 86 then (if j.val < 84 then (if j.val < 83 then 43 else 24) else (if j.val < 85 then 58 else 15)) else (if j.val < 88 then (if j.val < 87 then 110 else 74) else (if j.val < 89 then 116 else 61))))) else (if j.val < 105 then (if j.val < 97 then (if j.val < 93 then (if j.val < 91 then 28 else (if j.val < 92 then 0 else 33)) else (if j.val < 95 then (if j.val < 94 then 8 else 102) else (if j.val < 96 then 50 else 62))) else (if j.val < 101 then (if j.val < 99 then (if j.val < 98 then 44 else 30) else (if j.val < 100 then 12 else 76)) else (if j.val < 103 then (if j.val < 102 then 92 else 32) else (if j.val < 104 then 54 else 86)))) else (if j.val < 112 then (if j.val < 108 then (if j.val < 106 then 60 else (if j.val < 107 then 56 else 2)) else (if j.val < 110 then (if j.val < 109 then 26 else 14) else (if j.val < 111 then 80 else 72))) else (if j.val < 116 then (if j.val < 114 then (if j.val < 113 then 42 else 94) else (if j.val < 115 then 6 else 20)) else (if j.val < 118 then (if j.val < 117 then 64 else 40) else (if j.val < 119 then 34 else 10)))))))

private theorem kernelCompleteChecked : ∀ i : Fin 120,
    (⟨i⟩ : Source) * representative 0 =
      representative 0 * (⟨i⟩ : Source) →
    pairTop (⟨i⟩ : Source) = 1 → ∃ j, kernelRows j = i := by
  native_decide

private theorem topCompleteChecked : ∀ i : Fin 120,
    (⟨i⟩ : Source) * representative 0 =
      representative 0 * (⟨i⟩ : Source) →
    ∃ j, pairTop (⟨i⟩ : Source) = pairTop (⟨topRows j⟩ : Source) := by
  native_decide

def coordinates : FiniteCentralizerRowCoordinates
    pairTop (representative 0) 1 120 where
  kernelRows := kernelRows
  kernel_centralizes := by
    intro j
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    fin_cases j; decide +kernel
  kernel_mem := by decide +kernel
  kernelRows_injective := by decide +kernel
  kernel_complete := by
    intro i hi htop
    exact kernelCompleteChecked i
      (Subgroup.mem_centralizer_singleton_iff.mp hi) htop
  topRows := topRows
  top_centralizes := by
    intro j
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    fin_cases j <;> decide +kernel
  topImages_injective := by decide +kernel
  top_complete := by
    intro i hi
    exact topCompleteChecked i
      (Subgroup.mem_centralizer_singleton_iff.mp hi)

noncomputable def centralizer :
    FinitePairCentralizerCoordinateCertificate
      (Subgroup.centralizer ({representative 0} : Set Source)) 6 :=
  coordinates.toCoordinateCertificate 120 (by norm_num)

end C0
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

end
