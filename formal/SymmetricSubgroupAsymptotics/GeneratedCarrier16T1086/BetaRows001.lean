import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.BetaData

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

theorem betaNextChecked001 : ∀ i : Fin 256,
    (32 : ℕ) ≤ i.val → i.val < 64 → ∀ j : Fin 4, (betaSource ((betaNextTable i)[j.val]!), betaTarget ((betaNextTable i)[j.val]!)) = (betaSource i, betaTarget i) * (fun j => (betaGenerators j, betaImages j)) j := by decide +kernel

theorem betaWordsChecked001 : ∀ i : Fin 256,
    (32 : ℕ) ≤ i.val → i.val < 64 → (betaSource i, betaTarget i) = ((betaWordTable i).map (fun j => (betaGenerators j, betaImages j))).prod := by decide +kernel

theorem betaFirstKernelChecked001 : ∀ i : Fin 256,
    (32 : ℕ) ≤ i.val → i.val < 64 → betaSource i = 1 → betaTarget i = 1 := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
