import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare3
open BinaryRegular46ParityZeroOuterCarries
private def masks : Fin 12 → ℕ := ![0,1532495540865888858358347027150309183618739122183602176,1532495540865888858358347027150309183618739122183602176,0,4722366482869645213696,4722366482869712322560,4722366482869712322560,4722366482869913649152,4722366482869913649152,4722366482870718955520,4722366482870718955520,4722366482869645213696]
def certificate : BinaryLinearConstraintCertificate input
    (fun j : Fin 12 => target ⟨36 + j.val, by omega⟩) where
  support j := Finset.univ.filter fun i => (masks j).testBit i.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare3
