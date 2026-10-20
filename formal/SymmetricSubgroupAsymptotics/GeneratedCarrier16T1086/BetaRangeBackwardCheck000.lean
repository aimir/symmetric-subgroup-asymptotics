import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaMapsData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem betaRangeBackwardChecked000 : ∀ i : Fin 256,
    (0 : ℕ) ≤ i.val → i.val < 32 → quotientElement i = betaTarget (betaRangeBackward i) := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
