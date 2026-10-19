import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureSupplementData
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
set_option maxHeartbeats 1000000 in
theorem eightRows05_preimage_word : ∀ (r : Fin 8) (x : Fin 16), preimageWordElement (finProdFinEquiv ((5 : Fin 8), r)) x=preimageElements (finProdFinEquiv ((5 : Fin 8), r)) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_preimage_mul : ∀ (r : Fin 8) (j : Fin 64) (x : Fin 16), (preimageElements (finProdFinEquiv ((5 : Fin 8), r))*preimageElements j) x=preimageElements (preimageMul (finProdFinEquiv ((5 : Fin 8), r)) j) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_preimage_inverse : ∀ (r : Fin 8) (x : Fin 16), (preimageElements (finProdFinEquiv ((5 : Fin 8), r)))⁻¹ x=preimageElements (preimageInv (finProdFinEquiv ((5 : Fin 8), r))) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_preimage_conjugation : ∀ (r : Fin 8) (j : Fin 3) (x : Fin 16), (sourceGenerators j*preimageElements (finProdFinEquiv ((5 : Fin 8), r))*(sourceGenerators j)⁻¹) x=preimageElements (preimageConj j (finProdFinEquiv ((5 : Fin 8), r))) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_preimage_conj_inverse : ∀ (r : Fin 8) (j : Fin 3), preimageConj j (preimageInvConj j (finProdFinEquiv ((5 : Fin 8), r)))=(finProdFinEquiv ((5 : Fin 8), r)) ∧ preimageInvConj j (preimageConj j (finProdFinEquiv ((5 : Fin 8), r)))=(finProdFinEquiv ((5 : Fin 8), r)) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_preimage_code : ∀ r : Fin 8, pointCode (preimageElements (finProdFinEquiv ((5 : Fin 8), r)))=preimageCode (finProdFinEquiv ((5 : Fin 8), r)) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_preimage_code_injective : ∀ (r : Fin 8) (j : Fin 64), preimageCode (finProdFinEquiv ((5 : Fin 8), r))=preimageCode j → (finProdFinEquiv ((5 : Fin 8), r))=j := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_central_mod_N : ∀ (r : Fin 8) (j : Fin 3) (x : Fin 16), (sourceGenerators j*preimageElements (finProdFinEquiv ((5 : Fin 8), r))*(sourceGenerators j)⁻¹*(preimageElements (finProdFinEquiv ((5 : Fin 8), r)))⁻¹) x=normalElements (centralResidue j (finProdFinEquiv ((5 : Fin 8), r))) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_target_code : ∀ r : Fin 8, pointCode (targetState (finProdFinEquiv ((5 : Fin 6), r)))=targetCode (finProdFinEquiv ((5 : Fin 6), r)) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_target_code_injective : ∀ (r : Fin 8) (j : Fin 48), targetCode (finProdFinEquiv ((5 : Fin 6), r))=targetCode j → (finProdFinEquiv ((5 : Fin 6), r))=j := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_signature : ∀ r : Fin 8, cosetSignature (finProdFinEquiv ((5 : Fin 6), r))=signatureCode (finProdFinEquiv ((5 : Fin 6), r)) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_signature_injective : ∀ (r : Fin 8) (j : Fin 48), signatureCode (finProdFinEquiv ((5 : Fin 6), r))=signatureCode j → (finProdFinEquiv ((5 : Fin 6), r))=j := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_step_source : ∀ (r : Fin 8) (j : Fin 3) (x : Fin 16), (sourceState (step (finProdFinEquiv ((5 : Fin 6), r)) j)*preimageElements (stepResidue (finProdFinEquiv ((5 : Fin 6), r)) j)) x=(sourceState (finProdFinEquiv ((5 : Fin 6), r))*sourceGenerators j) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_step_target : ∀ (r : Fin 8) (j : Fin 3) (x : Fin 8), targetState (step (finProdFinEquiv ((5 : Fin 6), r)) j) x=(targetState (finProdFinEquiv ((5 : Fin 6), r))*targetGenerators j) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_inverse_source : ∀ (r : Fin 8) (x : Fin 16), (sourceState (inverse (finProdFinEquiv ((5 : Fin 6), r)))*preimageElements (inverseResidue (finProdFinEquiv ((5 : Fin 6), r)))) x=(sourceState (finProdFinEquiv ((5 : Fin 6), r)))⁻¹ x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows05_inverse_target : ∀ (r : Fin 8) (x : Fin 8), targetState (inverse (finProdFinEquiv ((5 : Fin 6), r))) x=(targetState (finProdFinEquiv ((5 : Fin 6), r)))⁻¹ x := by decide +kernel
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
