import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaMapsData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem alphaKernelForwardChecked011 : ∀ i : Fin 1024,
    (352 : ℕ) ≤ i.val → i.val < 384 → alphaTarget i = 1 → alphaSource i = axisElement (alphaKernelForward i) := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
