import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaMapsData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem alphaRangeBackwardChecked001 : ∀ i : Fin 256,
    (32 : ℕ) ≤ i.val → i.val < 64 → quotientElement i = alphaTarget (alphaRangeBackward i) := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
