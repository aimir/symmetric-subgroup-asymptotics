import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.CoverKernelData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem coverKernelNextChecked000 : ∀ i : Fin 1,
    (0 : ℕ) ≤ i.val → i.val < 1 → ∀ j : Fin 0, coverKernelElement ((coverKernelNextTable i)[j.val]!) = coverKernelElement i * coverKernelGenerators j := by decide +kernel

theorem coverKernelWordsChecked000 : ∀ i : Fin 1,
    (0 : ℕ) ≤ i.val → i.val < 1 → coverKernelElement i = ((coverKernelWordTable i).map coverKernelGenerators).prod := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
