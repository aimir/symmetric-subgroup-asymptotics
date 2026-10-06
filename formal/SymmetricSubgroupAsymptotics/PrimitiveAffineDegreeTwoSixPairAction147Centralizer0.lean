import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassInvariant
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 147: centralizer row 0

This is a resource-bounded split of the selected action-147 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

namespace C0

private def kernelRows (_j : Fin 1) : Fin 60 :=
  59

private def topRows (j : Fin 60) : Fin 60 :=
  (if j.val < 30 then (if j.val < 15 then (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then 59 else (if j.val < 2 then 22 else 49)) else (if j.val < 5 then (if j.val < 4 then 17 else 52) else (if j.val < 6 then 41 else 36))) else (if j.val < 11 then (if j.val < 9 then (if j.val < 8 then 29 else 32) else (if j.val < 10 then 13 else 53)) else (if j.val < 13 then (if j.val < 12 then 28 else 39) else (if j.val < 14 then 3 else 45)))) else (if j.val < 22 then (if j.val < 18 then (if j.val < 16 then 24 else (if j.val < 17 then 57 else 30)) else (if j.val < 20 then (if j.val < 19 then 42 else 7) else (if j.val < 21 then 43 else 14))) else (if j.val < 26 then (if j.val < 24 then (if j.val < 23 then 33 else 9) else (if j.val < 25 then 55 else 18)) else (if j.val < 28 then (if j.val < 27 then 51 else 2) else (if j.val < 29 then 46 else 35))))) else (if j.val < 45 then (if j.val < 37 then (if j.val < 33 then (if j.val < 31 then 56 else (if j.val < 32 then 47 else 44)) else (if j.val < 35 then (if j.val < 34 then 25 else 54) else (if j.val < 36 then 10 else 19))) else (if j.val < 41 then (if j.val < 39 then (if j.val < 38 then 6 else 23) else (if j.val < 40 then 0 else 34)) else (if j.val < 43 then (if j.val < 42 then 21 else 50) else (if j.val < 44 then 37 else 58)))) else (if j.val < 52 then (if j.val < 48 then (if j.val < 46 then 5 else (if j.val < 47 then 11 else 4)) else (if j.val < 50 then (if j.val < 49 then 27 else 15) else (if j.val < 51 then 38 else 16))) else (if j.val < 56 then (if j.val < 54 then (if j.val < 53 then 48 else 1) else (if j.val < 55 then 40 else 31)) else (if j.val < 58 then (if j.val < 57 then 26 else 8) else (if j.val < 59 then 20 else 12))))))

private theorem kernelCompleteChecked : ∀ i : Fin 60,
    (⟨i⟩ : Source) * representative 0 =
      representative 0 * (⟨i⟩ : Source) →
    pairTop (⟨i⟩ : Source) = 1 → ∃ j, kernelRows j = i := by
  native_decide

private theorem topCompleteChecked : ∀ i : Fin 60,
    (⟨i⟩ : Source) * representative 0 =
      representative 0 * (⟨i⟩ : Source) →
    ∃ j, pairTop (⟨i⟩ : Source) = pairTop (⟨topRows j⟩ : Source) := by
  native_decide

def coordinates : FiniteCentralizerRowCoordinates
    pairTop (representative 0) 1 60 where
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
  coordinates.toCoordinateCertificate 60 (by norm_num)

end C0
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

end
