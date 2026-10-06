import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassInvariant
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 147: centralizer row 4

This is a resource-bounded split of the selected action-147 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

namespace C4

private def kernelRows (_j : Fin 1) : Fin 60 :=
  59

private def topRows (j : Fin 3) : Fin 60 :=
  (if j.val < 1 then 59 else (if j.val < 2 then 39 else 43))

private theorem kernelCompleteChecked : ∀ i : Fin 60,
    (⟨i⟩ : Source) * representative 4 =
      representative 4 * (⟨i⟩ : Source) →
    pairTop (⟨i⟩ : Source) = 1 → ∃ j, kernelRows j = i := by
  native_decide

private theorem topCompleteChecked : ∀ i : Fin 60,
    (⟨i⟩ : Source) * representative 4 =
      representative 4 * (⟨i⟩ : Source) →
    ∃ j, pairTop (⟨i⟩ : Source) = pairTop (⟨topRows j⟩ : Source) := by
  native_decide

def coordinates : FiniteCentralizerRowCoordinates
    pairTop (representative 4) 1 3 where
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
  coordinates.toCoordinateCertificate 3 (by norm_num)

end C4
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

end
