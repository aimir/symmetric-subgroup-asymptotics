import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphData
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
set_option maxHeartbeats 1000000 in
theorem packet05_source_code : ∀ r : Fin 16, pointCode (targetState (finProdFinEquiv ((5 : Fin 12), r)))=sourceCode (finProdFinEquiv ((5 : Fin 12), r)) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem packet05_source_code_injective : ∀ (r : Fin 16) (j : Fin 192), sourceCode (finProdFinEquiv ((5 : Fin 12), r))=sourceCode j → (finProdFinEquiv ((5 : Fin 12), r))=j := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem packet05_signature : ∀ r : Fin 16, cosetSignature (finProdFinEquiv ((5 : Fin 12), r))=signatureCode (finProdFinEquiv ((5 : Fin 12), r)) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem packet05_signature_injective : ∀ (r : Fin 16) (j : Fin 192), signatureCode (finProdFinEquiv ((5 : Fin 12), r))=signatureCode j → (finProdFinEquiv ((5 : Fin 12), r))=j := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem packet05_step_source : ∀ (r : Fin 16) (j : Fin 4) (x : Fin 16),
  (sourceState (step (finProdFinEquiv ((5 : Fin 12), r)) j)*kernelElements (stepResidue (finProdFinEquiv ((5 : Fin 12), r)) j)) x=(sourceState (finProdFinEquiv ((5 : Fin 12), r))*sourceGenerators j) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem packet05_step_target : ∀ (r : Fin 16) (j : Fin 4) (x : Fin 12), targetState (step (finProdFinEquiv ((5 : Fin 12), r)) j) x=(targetState (finProdFinEquiv ((5 : Fin 12), r))*targetGenerators j) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem packet05_inverse_source : ∀ (r : Fin 16) (x : Fin 16),
  (sourceState (inverse (finProdFinEquiv ((5 : Fin 12), r)))*kernelElements (inverseResidue (finProdFinEquiv ((5 : Fin 12), r)))) x=(sourceState (finProdFinEquiv ((5 : Fin 12), r)))⁻¹ x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem packet05_inverse_target : ∀ (r : Fin 16) (x : Fin 12), targetState (inverse (finProdFinEquiv ((5 : Fin 12), r))) x=(targetState (finProdFinEquiv ((5 : Fin 12), r)))⁻¹ x := by decide +kernel
end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
