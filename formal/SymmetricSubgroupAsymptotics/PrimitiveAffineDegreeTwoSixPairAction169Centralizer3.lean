import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassInvariant
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 169: centralizer row 3

This is a resource-bounded split of the selected action-169 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

namespace C3

private def kernelRows (_j : Fin 1) : Fin 120 :=
  119

private def topRows (j : Fin 4) : Fin 120 :=
  (if j.val < 2 then (if j.val < 1 then 119 else 95) else (if j.val < 3 then 69 else 45))

private theorem kernelCompleteChecked : ∀ i : Fin 120,
    (⟨i⟩ : Source) * representative 3 =
      representative 3 * (⟨i⟩ : Source) →
    pairTop (⟨i⟩ : Source) = 1 → ∃ j, kernelRows j = i := by
  native_decide

private theorem topCompleteChecked : ∀ i : Fin 120,
    (⟨i⟩ : Source) * representative 3 =
      representative 3 * (⟨i⟩ : Source) →
    ∃ j, pairTop (⟨i⟩ : Source) = pairTop (⟨topRows j⟩ : Source) := by
  native_decide

def coordinates : FiniteCentralizerRowCoordinates
    pairTop (representative 3) 1 4 where
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
      (Subgroup.centralizer ({representative 3} : Set Source)) 6 :=
  coordinates.toCoordinateCertificate 4 (by norm_num)

end C3
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

end
