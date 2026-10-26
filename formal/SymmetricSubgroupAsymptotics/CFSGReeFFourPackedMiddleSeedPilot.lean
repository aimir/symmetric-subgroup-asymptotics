import SymmetricSubgroupAsymptotics.BinaryPackedMatrix
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedMiddleMatrix

/-! One selected existing26-dimensional seed is encoded in literal
binary rows. The only closed certificate is its676 decoded entries.
The product semantics is inherited from the generic packed-row theorem;
no whole chart, candidate classifier, or new group relation is claimed. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPackedMiddleSeedPilot
open BinaryPackedMatrix

def packedMiddle : Rows 26 := fun i=>
  ∑j∈CFSGReeFFourBinarySeedMiddleMatrix.rows i,2^j.val

theorem packedMiddle_entries : ∀i j : Fin 26,
    bit (packedMiddle i) j.val=CFSGReeFFourBinarySeedMiddleMatrix.matrix i j := by
  decide +kernel

theorem packedMiddle_decode : decode packedMiddle=CFSGReeFFourBinarySeedMiddleMatrix.matrix := by
  ext i j
  exact packedMiddle_entries i j

theorem packedMiddle_square_decode :
    decode (BinaryPackedMatrix.mul packedMiddle packedMiddle)=
      CFSGReeFFourBinarySeedMiddleMatrix.matrix*CFSGReeFFourBinarySeedMiddleMatrix.matrix := by
  rw [decode_mul,packedMiddle_decode]

end SymmetricSubgroupAsymptotics.CFSGReeFFourPackedMiddleSeedPilot
