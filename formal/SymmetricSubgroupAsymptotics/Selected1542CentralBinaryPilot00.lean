import SymmetricSubgroupAsymptotics.Selected1542CentralBinaryData
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
set_option maxHeartbeats 1000000 in
theorem centralBinaryPilot00_mul : ∀ (r : Fin 8) (j : Fin 64) (k : Fin 3), centralCoordinate (preimageMul (finProdFinEquiv ((0 : Fin 8),r)) j) k=centralCoordinate (finProdFinEquiv ((0 : Fin 8),r)) k*centralCoordinate j k := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem centralBinaryPilot00_zero : ∀ r : Fin 8, (∀ k : Fin 3, centralCoordinate (finProdFinEquiv ((0 : Fin 8),r)) k=1) ↔ isOriginalNormal (finProdFinEquiv ((0 : Fin 8),r))=true := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem centralBinaryPilot00_kernel : ∀ r : Fin 8, isOriginalNormal (finProdFinEquiv ((0 : Fin 8),r))=true ↔ ∃ n : Fin 8, ∀ x : Fin 16, preimageElements (finProdFinEquiv ((0 : Fin 8),r)) x=normalElements n x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem centralBinaryPilot00_identity : ∀ k : Fin 3, centralCoordinate 0 k=1 := by decide +kernel
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
