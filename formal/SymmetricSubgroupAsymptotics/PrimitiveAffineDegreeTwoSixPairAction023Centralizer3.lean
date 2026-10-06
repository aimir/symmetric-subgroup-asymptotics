import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023ClassInvariant
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 23: centralizer row 3

This is a resource-bounded split of the selected action-23 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023ClassPilot

namespace C3

private def kernelRows (_j : Fin 1) : Fin 12 :=
  11

private def topRows (j : Fin 3) : Fin 12 :=
  (if j.val < 1 then 11 else (if j.val < 2 then 2 else 7))

private theorem kernelCompleteChecked : ∀ i : Fin 12,
    (⟨i⟩ : Source) * representative 3 =
      representative 3 * (⟨i⟩ : Source) →
    pairTop (⟨i⟩ : Source) = 1 → ∃ j, kernelRows j = i := by
  native_decide

private theorem topCompleteChecked : ∀ i : Fin 12,
    (⟨i⟩ : Source) * representative 3 =
      representative 3 * (⟨i⟩ : Source) →
    ∃ j, pairTop (⟨i⟩ : Source) = pairTop (⟨topRows j⟩ : Source) := by
  native_decide

def coordinates : FiniteCentralizerRowCoordinates
    pairTop (representative 3) 1 3 where
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
  coordinates.toCoordinateCertificate 3 (by norm_num)

end C3
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023ClassPilot

end
