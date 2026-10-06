import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassInvariant
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 169: centralizer row 4

This is a resource-bounded split of the selected action-169 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

namespace C4

private def kernelRows (_j : Fin 1) : Fin 120 :=
  119

private def topRows (j : Fin 12) : Fin 120 :=
  (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 119 else (if j.val < 2 then 45 else 99)) else (if j.val < 4 then 65 else (if j.val < 5 then 98 else 11))) else (if j.val < 9 then (if j.val < 7 then 118 else (if j.val < 8 then 31 else 44)) else (if j.val < 10 then 30 else (if j.val < 11 then 64 else 10))))

private theorem kernelCompleteChecked : ∀ i : Fin 120,
    (⟨i⟩ : Source) * representative 4 =
      representative 4 * (⟨i⟩ : Source) →
    pairTop (⟨i⟩ : Source) = 1 → ∃ j, kernelRows j = i := by
  native_decide

private theorem topCompleteChecked : ∀ i : Fin 120,
    (⟨i⟩ : Source) * representative 4 =
      representative 4 * (⟨i⟩ : Source) →
    ∃ j, pairTop (⟨i⟩ : Source) = pairTop (⟨topRows j⟩ : Source) := by
  native_decide

def coordinates : FiniteCentralizerRowCoordinates
    pairTop (representative 4) 1 12 where
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
      (Subgroup.centralizer ({representative 4} : Set Source)) 6 :=
  coordinates.toCoordinateCertificate 12 (by norm_num)

end C4
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

end
