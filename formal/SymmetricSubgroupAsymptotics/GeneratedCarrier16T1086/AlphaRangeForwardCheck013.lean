import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaMapsData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem alphaRangeForwardChecked013 : ∀ i : Fin 1024,
    (416 : ℕ) ≤ i.val → i.val < 448 → alphaTarget i = quotientElement (alphaRangeForward i) := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
