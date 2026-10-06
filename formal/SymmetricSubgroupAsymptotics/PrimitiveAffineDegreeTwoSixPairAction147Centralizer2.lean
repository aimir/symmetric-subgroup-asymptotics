import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassInvariant
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 147: centralizer row 2

This is a resource-bounded split of the selected action-147 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

namespace C2

private def kernelRows (_j : Fin 1) : Fin 60 :=
  59

private def topRows (j : Fin 5) : Fin 60 :=
  (if j.val < 2 then (if j.val < 1 then 59 else 17) else (if j.val < 3 then 41 else (if j.val < 4 then 29 else 32)))

private theorem kernelCompleteChecked : ∀ i : Fin 60,
    (⟨i⟩ : Source) * representative 2 =
      representative 2 * (⟨i⟩ : Source) →
    pairTop (⟨i⟩ : Source) = 1 → ∃ j, kernelRows j = i := by
  native_decide

private theorem topCompleteChecked : ∀ i : Fin 60,
    (⟨i⟩ : Source) * representative 2 =
      representative 2 * (⟨i⟩ : Source) →
    ∃ j, pairTop (⟨i⟩ : Source) = pairTop (⟨topRows j⟩ : Source) := by
  native_decide

def coordinates : FiniteCentralizerRowCoordinates
    pairTop (representative 2) 1 5 where
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
      (Subgroup.centralizer ({representative 2} : Set Source)) 6 :=
  coordinates.toCoordinateCertificate 5 (by norm_num)

end C2
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

end
