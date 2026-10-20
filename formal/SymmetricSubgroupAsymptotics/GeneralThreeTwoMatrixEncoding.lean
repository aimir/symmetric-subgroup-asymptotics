import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups
import Mathlib.Data.Fin.VecNotation

/-!
# Nine-bit codes for the actual group GL(3,2)

Codes enumerate all binary matrices, including singular matrices.  Only
the actual invertible generators and reachable code rows are used by a
Cayley certificate.  Faithfulness therefore concerns the original matrix
group, with no abstract recognition or permutation-table premise.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoMatrixEncoding

abbrev Ambient := StandardThreeDimensionalLinearGroups.GeneralThree 2
abbrev Mat := Matrix (Fin 3) (Fin 3) (ZMod 2)

/-- Row i occupies bits 3i, 3i+1, 3i+2. -/
def encode (A : Mat) : Fin 512 :=
  finFunctionFinEquiv (fun i : Fin 3 =>
    finFunctionFinEquiv (fun j : Fin 3 => (ZMod.finEquiv 2).symm (A i j)))

def decode (c : Fin 512) : Mat :=
  fun i j => ZMod.finEquiv 2
    (finFunctionFinEquiv.symm ((finFunctionFinEquiv.symm c) i) j)

@[simp] theorem decode_encode (A : Mat) : decode (encode A) = A := by
  ext i j
  simp [decode, encode]

theorem encode_injective : Function.Injective encode := by
  intro A B h
  simpa only [decode_encode] using congrArg decode h

def generator0 : Ambient where
  val := ![![1, 1, 0], ![0, 1, 0], ![0, 0, 1]]
  inv := ![![1, 1, 0], ![0, 1, 0], ![0, 0, 1]]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def generator1 : Ambient where
  val := ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]
  inv := ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def generators : Fin 2 → Ambient := ![generator0, generator1]

/-- Right multiplication is computed on nine-bit matrix codes; an invalid
code is never asserted to represent an invertible matrix. -/
def encoding : GeneratorEncoding generators (Fin 512) where
  encode g := encode g.val
  injective := fun _ _ h => Units.ext (encode_injective h)
  one := encode 1
  encode_one := rfl
  step c j := encode (decode c * (generators j).val)
  encode_step g j := by
    change encode (g.val * (generators j).val) =
      encode (decode (encode g.val) * (generators j).val)
    rw [decode_encode]

end SymmetricSubgroupAsymptotics.GeneralThreeTwoMatrixEncoding

end
