import SymmetricSubgroupAsymptotics.Selected1542CentralBinaryPilot00
import SymmetricSubgroupAsymptotics.Selected1542CentralBinaryRows01
import SymmetricSubgroupAsymptotics.Selected1542CentralBinaryRows02
import SymmetricSubgroupAsymptotics.Selected1542CentralBinaryRows03
import SymmetricSubgroupAsymptotics.Selected1542CentralBinaryRows04
import SymmetricSubgroupAsymptotics.Selected1542CentralBinaryRows05
import SymmetricSubgroupAsymptotics.Selected1542CentralBinaryRows06
import SymmetricSubgroupAsymptotics.Selected1542CentralBinaryRows07
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
private theorem assemble (Q : Fin 64 → Prop)
    (h0 : ∀ r : Fin 8, Q (finProdFinEquiv ((0 : Fin 8),r)))
    (h1 : ∀ r : Fin 8, Q (finProdFinEquiv ((1 : Fin 8),r)))
    (h2 : ∀ r : Fin 8, Q (finProdFinEquiv ((2 : Fin 8),r)))
    (h3 : ∀ r : Fin 8, Q (finProdFinEquiv ((3 : Fin 8),r)))
    (h4 : ∀ r : Fin 8, Q (finProdFinEquiv ((4 : Fin 8),r)))
    (h5 : ∀ r : Fin 8, Q (finProdFinEquiv ((5 : Fin 8),r)))
    (h6 : ∀ r : Fin 8, Q (finProdFinEquiv ((6 : Fin 8),r)))
    (h7 : ∀ r : Fin 8, Q (finProdFinEquiv ((7 : Fin 8),r)))
    (i : Fin 64) : Q i := by
  obtain ⟨⟨k,r⟩,rfl⟩ := (finProdFinEquiv : Fin 8 × Fin 8 ≃ Fin 64).surjective i
  fin_cases k
  · exact h0 r
  · exact h1 r
  · exact h2 r
  · exact h3 r
  · exact h4 r
  · exact h5 r
  · exact h6 r
  · exact h7 r

theorem centralBinary_all_mul (i : Fin 64) : ∀ (j : Fin 64) (k : Fin 3), centralCoordinate (preimageMul i j) k=centralCoordinate i k*centralCoordinate j k :=
  assemble (fun i => ∀ (j : Fin 64) (k : Fin 3), centralCoordinate (preimageMul i j) k=centralCoordinate i k*centralCoordinate j k) centralBinaryPilot00_mul centralBinaryRows01_mul centralBinaryRows02_mul centralBinaryRows03_mul centralBinaryRows04_mul centralBinaryRows05_mul centralBinaryRows06_mul centralBinaryRows07_mul i

theorem centralBinary_all_zero (i : Fin 64) : (∀ k : Fin 3, centralCoordinate i k=1) ↔ isOriginalNormal i=true :=
  assemble (fun i => (∀ k : Fin 3, centralCoordinate i k=1) ↔ isOriginalNormal i=true) centralBinaryPilot00_zero centralBinaryRows01_zero centralBinaryRows02_zero centralBinaryRows03_zero centralBinaryRows04_zero centralBinaryRows05_zero centralBinaryRows06_zero centralBinaryRows07_zero i

theorem centralBinary_all_kernel (i : Fin 64) : isOriginalNormal i=true ↔ ∃ n : Fin 8, ∀ x : Fin 16, preimageElements i x=normalElements n x :=
  assemble (fun i => isOriginalNormal i=true ↔ ∃ n : Fin 8, ∀ x : Fin 16, preimageElements i x=normalElements n x) centralBinaryPilot00_kernel centralBinaryRows01_kernel centralBinaryRows02_kernel centralBinaryRows03_kernel centralBinaryRows04_kernel centralBinaryRows05_kernel centralBinaryRows06_kernel centralBinaryRows07_kernel i
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
