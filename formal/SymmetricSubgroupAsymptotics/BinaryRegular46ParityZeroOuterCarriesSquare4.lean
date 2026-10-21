import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare4
open BinaryRegular46ParityZeroOuterCarries
private def masks : Fin 12 → ℕ := ![3064991081731777716716694054300618367237478244367204352,0,3064991081731777716716694054300618367237478244367204352,0,38685626227668142180532224,38685626227668133590597632,38685626227668142180532224,38685626227668202310074368,38685626227668271029551104,38685626227668202310074368,38685626227668271029551104,38685626227668133590597632]
def certificate : BinaryLinearConstraintCertificate input
    (fun j : Fin 12 => target ⟨48 + j.val, by omega⟩) where
  support j := Finset.univ.filter fun i => (masks j).testBit i.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare4
