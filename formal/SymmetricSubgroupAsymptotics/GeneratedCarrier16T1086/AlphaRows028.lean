import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AlphaData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem alphaNextChecked028 : ∀ i : Fin 1024,
    (896 : ℕ) ≤ i.val → i.val < 928 → ∀ j : Fin 4, (alphaSource ((alphaNextTable i)[j.val]!), alphaTarget ((alphaNextTable i)[j.val]!)) = (alphaSource i, alphaTarget i) * (fun j => (alphaGenerators j, alphaImages j)) j := by decide +kernel

theorem alphaWordsChecked028 : ∀ i : Fin 1024,
    (896 : ℕ) ≤ i.val → i.val < 928 → (alphaSource i, alphaTarget i) = ((alphaWordTable i).map (fun j => (alphaGenerators j, alphaImages j))).prod := by decide +kernel

theorem alphaFirstKernelChecked028 : ∀ i : Fin 1024,
    (896 : ℕ) ≤ i.val → i.val < 928 → alphaSource i = 1 → alphaTarget i = 1 := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
