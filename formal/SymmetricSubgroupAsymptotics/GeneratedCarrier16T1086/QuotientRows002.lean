import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.QuotientData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem quotientNextChecked002 : ∀ i : Fin 256,
    (64 : ℕ) ≤ i.val → i.val < 96 → ∀ j : Fin 4, quotientElement ((quotientNextTable i)[j.val]!) = quotientElement i * quotientGenerators j := by decide +kernel

theorem quotientWordsChecked002 : ∀ i : Fin 256,
    (64 : ℕ) ≤ i.val → i.val < 96 → quotientElement i = ((quotientWordTable i).map quotientGenerators).prod := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
