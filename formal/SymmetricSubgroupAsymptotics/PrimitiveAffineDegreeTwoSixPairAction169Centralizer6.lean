import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassInvariant
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 169: centralizer row 6

This is a resource-bounded split of the selected action-169 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

namespace C6

private def kernelRows (_j : Fin 1) : Fin 120 :=
  119

private def topRows (j : Fin 6) : Fin 120 :=
  (if j.val < 3 then (if j.val < 1 then 119 else (if j.val < 2 then 79 else 87)) else (if j.val < 4 then 52 else (if j.val < 5 then 12 else 20)))

private theorem kernelCompleteChecked : ∀ i : Fin 120,
    (⟨i⟩ : Source) * representative 6 =
      representative 6 * (⟨i⟩ : Source) →
    pairTop (⟨i⟩ : Source) = 1 → ∃ j, kernelRows j = i := by
  native_decide

private theorem topCompleteChecked : ∀ i : Fin 120,
    (⟨i⟩ : Source) * representative 6 =
      representative 6 * (⟨i⟩ : Source) →
    ∃ j, pairTop (⟨i⟩ : Source) = pairTop (⟨topRows j⟩ : Source) := by
  native_decide

def coordinates : FiniteCentralizerRowCoordinates
    pairTop (representative 6) 1 6 where
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
      (Subgroup.centralizer ({representative 6} : Set Source)) 6 :=
  coordinates.toCoordinateCertificate 6 (by norm_num)

end C6
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

end
