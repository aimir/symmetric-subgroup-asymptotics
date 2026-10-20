import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaMapsData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem betaKernelForwardChecked005 : ∀ i : Fin 256,
    (160 : ℕ) ≤ i.val → i.val < 192 → betaTarget i = 1 → betaSource i = coverKernelElement (betaKernelForward i) := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
