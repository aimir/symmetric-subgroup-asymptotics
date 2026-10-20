import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AxisData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem axisNextChecked000 : ∀ i : Fin 4,
    (0 : ℕ) ≤ i.val → i.val < 4 → ∀ j : Fin 2, axisElement ((axisNextTable i)[j.val]!) = axisElement i * axisGenerators j := by decide +kernel

theorem axisWordsChecked000 : ∀ i : Fin 4,
    (0 : ℕ) ≤ i.val → i.val < 4 → axisElement i = ((axisWordTable i).map axisGenerators).prod := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
