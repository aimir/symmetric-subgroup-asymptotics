import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaMapsData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem betaRangeForwardChecked005 : ∀ i : Fin 256,
    (160 : ℕ) ≤ i.val → i.val < 192 → betaTarget i = quotientElement (betaRangeForward i) := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
