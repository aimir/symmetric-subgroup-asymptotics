import SymmetricSubgroupAsymptotics.Selected1542QuotientStructureSupplementData
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
set_option maxHeartbeats 1000000 in
theorem eightRows07_preimage_word : ∀ (r : Fin 8) (x : Fin 16), preimageWordElement (finProdFinEquiv ((7 : Fin 8), r)) x=preimageElements (finProdFinEquiv ((7 : Fin 8), r)) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows07_preimage_mul : ∀ (r : Fin 8) (j : Fin 64) (x : Fin 16), (preimageElements (finProdFinEquiv ((7 : Fin 8), r))*preimageElements j) x=preimageElements (preimageMul (finProdFinEquiv ((7 : Fin 8), r)) j) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows07_preimage_inverse : ∀ (r : Fin 8) (x : Fin 16), (preimageElements (finProdFinEquiv ((7 : Fin 8), r)))⁻¹ x=preimageElements (preimageInv (finProdFinEquiv ((7 : Fin 8), r))) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows07_preimage_conjugation : ∀ (r : Fin 8) (j : Fin 3) (x : Fin 16), (sourceGenerators j*preimageElements (finProdFinEquiv ((7 : Fin 8), r))*(sourceGenerators j)⁻¹) x=preimageElements (preimageConj j (finProdFinEquiv ((7 : Fin 8), r))) x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows07_preimage_conj_inverse : ∀ (r : Fin 8) (j : Fin 3), preimageConj j (preimageInvConj j (finProdFinEquiv ((7 : Fin 8), r)))=(finProdFinEquiv ((7 : Fin 8), r)) ∧ preimageInvConj j (preimageConj j (finProdFinEquiv ((7 : Fin 8), r)))=(finProdFinEquiv ((7 : Fin 8), r)) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows07_preimage_code : ∀ r : Fin 8, pointCode (preimageElements (finProdFinEquiv ((7 : Fin 8), r)))=preimageCode (finProdFinEquiv ((7 : Fin 8), r)) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows07_preimage_code_injective : ∀ (r : Fin 8) (j : Fin 64), preimageCode (finProdFinEquiv ((7 : Fin 8), r))=preimageCode j → (finProdFinEquiv ((7 : Fin 8), r))=j := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem eightRows07_central_mod_N : ∀ (r : Fin 8) (j : Fin 3) (x : Fin 16), (sourceGenerators j*preimageElements (finProdFinEquiv ((7 : Fin 8), r))*(sourceGenerators j)⁻¹*(preimageElements (finProdFinEquiv ((7 : Fin 8), r)))⁻¹) x=normalElements (centralResidue j (finProdFinEquiv ((7 : Fin 8), r))) x := by decide +kernel
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
