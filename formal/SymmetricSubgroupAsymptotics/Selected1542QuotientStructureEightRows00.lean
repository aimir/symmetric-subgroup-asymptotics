import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureSupplementData
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
set_option maxHeartbeats 1000000 in
theorem eightRows00_preimage_word : ∀ (r : Fin 8) (x : Fin 16), preimageWordElement (finProdFinEquiv ((0 : Fin 8), r)) x=preimageElements (finProdFinEquiv ((0 : Fin 8), r)) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_preimage_mul : ∀ (r : Fin 8) (j : Fin 64) (x : Fin 16), (preimageElements (finProdFinEquiv ((0 : Fin 8), r))*preimageElements j) x=preimageElements (preimageMul (finProdFinEquiv ((0 : Fin 8), r)) j) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_preimage_inverse : ∀ (r : Fin 8) (x : Fin 16), (preimageElements (finProdFinEquiv ((0 : Fin 8), r)))⁻¹ x=preimageElements (preimageInv (finProdFinEquiv ((0 : Fin 8), r))) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_preimage_conjugation : ∀ (r : Fin 8) (j : Fin 3) (x : Fin 16), (sourceGenerators j*preimageElements (finProdFinEquiv ((0 : Fin 8), r))*(sourceGenerators j)⁻¹) x=preimageElements (preimageConj j (finProdFinEquiv ((0 : Fin 8), r))) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_preimage_conj_inverse : ∀ (r : Fin 8) (j : Fin 3), preimageConj j (preimageInvConj j (finProdFinEquiv ((0 : Fin 8), r)))=(finProdFinEquiv ((0 : Fin 8), r)) ∧ preimageInvConj j (preimageConj j (finProdFinEquiv ((0 : Fin 8), r)))=(finProdFinEquiv ((0 : Fin 8), r)) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_preimage_code : ∀ r : Fin 8, pointCode (preimageElements (finProdFinEquiv ((0 : Fin 8), r)))=preimageCode (finProdFinEquiv ((0 : Fin 8), r)) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_preimage_code_injective : ∀ (r : Fin 8) (j : Fin 64), preimageCode (finProdFinEquiv ((0 : Fin 8), r))=preimageCode j → (finProdFinEquiv ((0 : Fin 8), r))=j := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_central_mod_N : ∀ (r : Fin 8) (j : Fin 3) (x : Fin 16), (sourceGenerators j*preimageElements (finProdFinEquiv ((0 : Fin 8), r))*(sourceGenerators j)⁻¹*(preimageElements (finProdFinEquiv ((0 : Fin 8), r)))⁻¹) x=normalElements (centralResidue j (finProdFinEquiv ((0 : Fin 8), r))) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_normal_word : ∀ (i : Fin 8) (x : Fin 16), normalWordElement i x=normalElements i x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_normal_mul : ∀ (i j : Fin 8) (x : Fin 16), (normalElements i*normalElements j) x=normalElements (normalMul i j) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_normal_inverse : ∀ (i : Fin 8) (x : Fin 16), (normalElements i)⁻¹ x=normalElements (normalInv i) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_normal_conjugation : ∀ (i : Fin 8) (j : Fin 3) (x : Fin 16), (sourceGenerators j*normalElements i*(sourceGenerators j)⁻¹) x=normalElements (normalConj j i) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_normal_conj_inverse : ∀ (i : Fin 8) (j : Fin 3), normalConj j (normalInvConj j i)=i ∧ normalInvConj j (normalConj j i)=i := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_normal_code : ∀ i : Fin 8, pointCode (normalElements i)=normalCode i := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_normal_code_injective : ∀ i j : Fin 8, normalCode i=normalCode j → i=j := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_normal_in_preimage : ∀ (i : Fin 8) (x : Fin 16), normalElements i x=preimageElements (normalInPreimage i) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_target_code : ∀ r : Fin 8, pointCode (targetState (finProdFinEquiv ((0 : Fin 6), r)))=targetCode (finProdFinEquiv ((0 : Fin 6), r)) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_target_code_injective : ∀ (r : Fin 8) (j : Fin 48), targetCode (finProdFinEquiv ((0 : Fin 6), r))=targetCode j → (finProdFinEquiv ((0 : Fin 6), r))=j := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_signature : ∀ r : Fin 8, cosetSignature (finProdFinEquiv ((0 : Fin 6), r))=signatureCode (finProdFinEquiv ((0 : Fin 6), r)) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_signature_injective : ∀ (r : Fin 8) (j : Fin 48), signatureCode (finProdFinEquiv ((0 : Fin 6), r))=signatureCode j → (finProdFinEquiv ((0 : Fin 6), r))=j := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_step_source : ∀ (r : Fin 8) (j : Fin 3) (x : Fin 16), (sourceState (step (finProdFinEquiv ((0 : Fin 6), r)) j)*preimageElements (stepResidue (finProdFinEquiv ((0 : Fin 6), r)) j)) x=(sourceState (finProdFinEquiv ((0 : Fin 6), r))*sourceGenerators j) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_step_target : ∀ (r : Fin 8) (j : Fin 3) (x : Fin 8), targetState (step (finProdFinEquiv ((0 : Fin 6), r)) j) x=(targetState (finProdFinEquiv ((0 : Fin 6), r))*targetGenerators j) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_inverse_source : ∀ (r : Fin 8) (x : Fin 16), (sourceState (inverse (finProdFinEquiv ((0 : Fin 6), r)))*preimageElements (inverseResidue (finProdFinEquiv ((0 : Fin 6), r)))) x=(sourceState (finProdFinEquiv ((0 : Fin 6), r)))⁻¹ x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows00_inverse_target : ∀ (r : Fin 8) (x : Fin 8), targetState (inverse (finProdFinEquiv ((0 : Fin 6), r))) x=(targetState (finProdFinEquiv ((0 : Fin 6), r)))⁻¹ x := by decide +kernel
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
