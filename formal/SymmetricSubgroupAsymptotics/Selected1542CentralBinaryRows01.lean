import SymmetricSubgroupAsymptotics.Selected1542CentralBinaryData
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
set_option maxHeartbeats 1000000 in
theorem centralBinaryRows01_mul : ∀ (r : Fin 8) (j : Fin 64) (k : Fin 3), centralCoordinate (preimageMul (finProdFinEquiv ((1 : Fin 8),r)) j) k=centralCoordinate (finProdFinEquiv ((1 : Fin 8),r)) k*centralCoordinate j k := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem centralBinaryRows01_zero : ∀ r : Fin 8, (∀ k : Fin 3, centralCoordinate (finProdFinEquiv ((1 : Fin 8),r)) k=1) ↔ isOriginalNormal (finProdFinEquiv ((1 : Fin 8),r))=true := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem centralBinaryRows01_kernel : ∀ r : Fin 8, isOriginalNormal (finProdFinEquiv ((1 : Fin 8),r))=true ↔ ∃ n : Fin 8, ∀ x : Fin 16, preimageElements (finProdFinEquiv ((1 : Fin 8),r)) x=normalElements n x := by decide +kernel
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
