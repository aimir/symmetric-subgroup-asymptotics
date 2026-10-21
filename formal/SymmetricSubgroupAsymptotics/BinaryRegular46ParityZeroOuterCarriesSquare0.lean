import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare0
open BinaryRegular46ParityZeroOuterCarries
private def masks : Fin 12 → ℕ := ![75557863725914323419136,309485009821345068724781057,309560567685070983048200192,0,0,0,0,0,0,0,0,0]
def certificate : BinaryLinearConstraintCertificate input
    (fun j : Fin 12 => target ⟨0 + j.val, by omega⟩) where
  support j := Finset.univ.filter fun i => (masks j).testBit i.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare0
