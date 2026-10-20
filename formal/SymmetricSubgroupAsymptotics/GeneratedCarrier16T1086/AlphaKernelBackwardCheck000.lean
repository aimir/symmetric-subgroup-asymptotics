import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaMapsData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem alphaKernelBackwardChecked000 : ∀ i : Fin 4,
    (0 : ℕ) ≤ i.val → i.val < 4 → alphaSource (alphaKernelBackward i) = axisElement i ∧ alphaTarget (alphaKernelBackward i) = 1 := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
